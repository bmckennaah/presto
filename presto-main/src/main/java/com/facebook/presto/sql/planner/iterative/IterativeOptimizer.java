/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.facebook.presto.sql.planner.iterative;

import com.facebook.presto.Session;
import com.facebook.presto.SystemSessionProperties;
import com.facebook.presto.cost.CachingCostProvider;
import com.facebook.presto.cost.CachingStatsProvider;
import com.facebook.presto.cost.CostCalculator;
import com.facebook.presto.cost.CostProvider;
import com.facebook.presto.cost.StatsCalculator;
import com.facebook.presto.cost.StatsProvider;
import com.facebook.presto.matching.Match;
import com.facebook.presto.matching.Matcher;
import com.facebook.presto.metadata.Metadata;
import com.facebook.presto.spi.PrestoException;
import com.facebook.presto.spi.VariableAllocator;
import com.facebook.presto.spi.WarningCollector;
import com.facebook.presto.spi.eventlistener.PlanOptimizerInformation;
import com.facebook.presto.spi.plan.LogicalPropertiesProvider;
import com.facebook.presto.spi.plan.PlanNode;
import com.facebook.presto.spi.plan.PlanNodeIdAllocator;
import com.facebook.presto.sql.planner.OptTrace;
import com.facebook.presto.sql.planner.PlannerUtils;
import com.facebook.presto.sql.planner.RuleStatsRecorder;
import com.facebook.presto.sql.planner.TypeProvider;
import com.facebook.presto.sql.planner.optimizations.PlanOptimizer;
import com.google.common.collect.ImmutableList;
import io.airlift.units.Duration;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

import static com.facebook.presto.SystemSessionProperties.isEnableOptimizerTrace;
import static com.facebook.presto.SystemSessionProperties.isVerboseOptimizerInfoEnabled;
import static com.facebook.presto.common.RuntimeUnit.NANO;
import static com.facebook.presto.spi.StandardErrorCode.OPTIMIZER_TIMEOUT;
import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static java.lang.String.format;
import static java.util.Objects.requireNonNull;
import static java.util.concurrent.TimeUnit.NANOSECONDS;

public class IterativeOptimizer
        implements PlanOptimizer
{
    private final Metadata metadata;
    private final RuleStatsRecorder stats;
    private final StatsCalculator statsCalculator;
    private final CostCalculator costCalculator;
    private final List<PlanOptimizer> legacyRules;
    private final RuleIndex ruleIndex;
    private final Optional<LogicalPropertiesProvider> logicalPropertiesProvider;

    public IterativeOptimizer(Metadata metadata, RuleStatsRecorder stats, StatsCalculator statsCalculator, CostCalculator costCalculator, Set<Rule<?>> rules)
    {
        this(metadata, stats, statsCalculator, costCalculator, ImmutableList.of(), Optional.empty(), rules);
    }

    public IterativeOptimizer(Metadata metadata, RuleStatsRecorder stats, StatsCalculator statsCalculator, CostCalculator costCalculator, Optional<LogicalPropertiesProvider> logicalPropertiesProvider, Set<Rule<?>> rules)
    {
        this(metadata, stats, statsCalculator, costCalculator, ImmutableList.of(), logicalPropertiesProvider, rules);
    }

    public IterativeOptimizer(Metadata metadata, RuleStatsRecorder stats, StatsCalculator statsCalculator, CostCalculator costCalculator, List<PlanOptimizer> legacyRules, Set<Rule<?>> newRules)
    {
        this(metadata, stats, statsCalculator, costCalculator, legacyRules, Optional.empty(), newRules);
    }

    public IterativeOptimizer(Metadata metadata, RuleStatsRecorder stats, StatsCalculator statsCalculator, CostCalculator costCalculator, List<PlanOptimizer> legacyRules, Optional<LogicalPropertiesProvider> logicalPropertiesProvider, Set<Rule<?>> newRules)
    {
        this.metadata = requireNonNull(metadata, "metadata is null");
        this.stats = requireNonNull(stats, "stats is null");
        this.statsCalculator = requireNonNull(statsCalculator, "statsCalculator is null");
        this.costCalculator = requireNonNull(costCalculator, "costCalculator is null");
        this.legacyRules = ImmutableList.copyOf(legacyRules);
        this.ruleIndex = RuleIndex.builder()
                .register(newRules)
                .build();
        this.logicalPropertiesProvider = requireNonNull(logicalPropertiesProvider, "logicalPropertiesProvider is null");

        stats.registerAll(newRules);
    }

    @Override
    public PlanNode optimize(PlanNode plan, Session session, TypeProvider types, VariableAllocator variableAllocator, PlanNodeIdAllocator idAllocator, WarningCollector warningCollector)
    {
        // only disable new rules if we have legacy rules to fall back to
        if (!SystemSessionProperties.isNewOptimizerEnabled(session) && !legacyRules.isEmpty()) {
            for (PlanOptimizer optimizer : legacyRules) {
                plan = optimizer.optimize(plan, session, TypeProvider.viewOf(variableAllocator.getVariables()), variableAllocator, idAllocator, warningCollector);
            }

            return plan;
        }

        Memo memo;
        if (SystemSessionProperties.isExploitConstraints(session)) {
            memo = new Memo(idAllocator, plan, logicalPropertiesProvider);
        }
        else {
            memo = new Memo(idAllocator, plan, Optional.empty());
        }

        Lookup lookup = Lookup.from(planNode -> Stream.of(memo.resolve(planNode)));
        Matcher matcher = new PlanNodeMatcher(lookup);

        Duration timeout = SystemSessionProperties.getOptimizerTimeout(session);

        StatsProvider statsProvider = new CachingStatsProvider(
                statsCalculator,
                Optional.of(memo),
                lookup,
                session,
                TypeProvider.viewOf(variableAllocator.getVariables()));
        CostProvider costProvider = new CachingCostProvider(costCalculator, statsProvider, Optional.of(memo), session);
        Context context = new Context(memo, lookup, idAllocator, variableAllocator, System.nanoTime(), timeout.toMillis(), session, warningCollector, costProvider, statsProvider, metadata, types);

        context.allocOptTrace("/tmp");
        OptTrace.assignTraceIds(session.getOptTrace(), context.memo.getNode(memo.getRootGroup()), null);

        boolean planChanged = exploreGroup(memo.getRootGroup(), context, matcher);
        context.collectOptimizerInformation();

        if (!planChanged) {
            return plan;
        }

        return memo.extract();
    }

    private boolean exploreGroup(int group, Context context, Matcher matcher)
    {
        OptTrace.begin(context.session.getOptTrace(), "exploreGroup : group %d", group);
        // tracks whether this group or any children groups change as
        // this method executes
        boolean progress = exploreNode(group, context, matcher);

        while (exploreChildren(group, context, matcher)) {
            progress = true;

            // if children changed, try current group again
            // in case we can match additional rules
            if (!exploreNode(group, context, matcher)) {
                // no additional matches, so bail out
                break;
            }
        }

        OptTrace.end(context.session.getOptTrace(), "exploreGroup : group %s , progress %s", group, progress ? "true" : "false");

        return progress;
    }

    private boolean exploreNode(int group, Context context, Matcher matcher)
    {
        PlanNode node = context.memo.getNode(group);
        OptTrace.begin(context.session.getOptTrace(), "exploreNode : group %d , node id %s , %s",
                group, node.getId().getId(), node.getClass().getSimpleName());

        boolean done = false;
        boolean progress = false;

        while (!done) {
            context.checkTimeoutNotExhausted();

            done = true;
            Iterator<Rule<?>> possiblyMatchingRules = ruleIndex.getCandidates(node).iterator();
            while (possiblyMatchingRules.hasNext()) {
                Rule<?> rule = possiblyMatchingRules.next();

                if (!rule.isEnabled(context.session)) {
                    if (isVerboseOptimizerInfoEnabled(context.session) && isApplicable(node, rule, matcher, context)) {
                        context.addRulesApplicable(rule.getClass().getSimpleName());
                    }
                    continue;
                }

                OptTrace.msg(context.session.getOptTrace(), "Next enabled rule : %s", true, rule.getClass().getSimpleName());

                Rule.Result result = transform(node, rule, matcher, context);

                if (result.getTransformedPlan().isPresent()) {
                    // If we rewrite a plan node, topmost node should remain statistically equivalent.
                    PlanNode transformedNode = result.getTransformedPlan().get();
                    PlanNode resolvedtransformedNode = context.lookup.resolve(result.getTransformedPlan().get());
                    if (node.getStatsEquivalentPlanNode().isPresent() && !resolvedtransformedNode.getStatsEquivalentPlanNode().isPresent()) {
                        if (transformedNode instanceof GroupReference) {
                            context.memo.assignStatsEquivalentPlanNode((GroupReference) transformedNode, node.getStatsEquivalentPlanNode());
                        }
                        else {
                            transformedNode = transformedNode.assignStatsEquivalentPlanNode(node.getStatsEquivalentPlanNode());
                        }
                    }

                    if (context.session.getOptTrace().isPresent()) {
                        OptTrace optTrace = context.session.getOptTrace().get();
                        optTrace.begin("Memo.replace (applied rule %s)", rule.getClass().getSimpleName());
                        optTrace.msg("Old node : group %s , node id %s , %s", true,
                                group, node.getId(), node.getClass().getSimpleName());
                        optTrace.tracePlanNode(node, 1, "", 1, null);
                        optTrace.traceMemo();
                        optTrace.msg("group %s node id %s ===========> group %s new node %s", true, group, node.getId(), group, transformedNode.getId());
                        optTrace.tracePlanNode(transformedNode, 1, "", 1, null);
                    }

                    context.addRulesTriggered(rule.getClass().getSimpleName(), node, transformedNode);
                    node = context.memo.replace(group, transformedNode, rule.getClass().getName());

                    OptTrace.msg(context.session.getOptTrace(), "New node : group %s , node id %s , %s", true,
                            group, node.getId(), node.getClass().getSimpleName());

                    OptTrace.end(context.session.getOptTrace(), "Memo.replace(applied rule %s)", rule.getClass().getSimpleName());

                    done = false;
                    progress = true;
                }
            }
        }

        OptTrace.end(context.session.getOptTrace(), "exploreNode : group %s , node id %s , %s",
                group, node.getId().getId(), node.getClass().getSimpleName());

        return progress;
    }

    private <T> Rule.Result transform(PlanNode node, Rule<T> rule, Matcher matcher, Context context)
    {
        Rule.Result result;

        OptTrace.begin(context.session.getOptTrace(), "transform");

        Match<T> match = matcher.match(rule.getPattern(), node);

        if (match.isEmpty()) {
            OptTrace.msg(context.session.getOptTrace(), "no match : rule %s", true, rule.getClass().getSimpleName());
            OptTrace.end(context.session.getOptTrace(), "transform");
            return Rule.Result.empty();
        }

        long duration;
        try {
            long start = System.nanoTime();
            OptTrace.begin(context.session.getOptTrace(), "rule.apply : %s", rule.getClass().getSimpleName());
            result = rule.apply(match.value(), match.captures(), ruleContext(context));
            OptTrace.end(context.session.getOptTrace(), "rule.apply : %s , applied? %s", rule.getClass().getSimpleName(),
                    result.isEmpty() ? "false" : "true");
            duration = System.nanoTime() - start;
        }
        catch (RuntimeException e) {
            stats.recordFailure(rule);
            throw e;
        }
        stats.record(rule, duration, !result.isEmpty());
        if (SystemSessionProperties.isVerboseRuntimeStatsEnabled(context.session)) {
            context.session.getRuntimeStats().addMetricValue(String.format("rule%sTimeNanos", rule.getClass().getSimpleName()), NANO, duration);
        }

        OptTrace.end(context.session.getOptTrace(), "transform");

        return result;
    }

    private <T> boolean isApplicable(PlanNode node, Rule<T> rule, Matcher matcher, Context context)
    {
        Match<T> match = matcher.match(rule.getPattern(), node);
        if (match.isEmpty()) {
            return false;
        }

        Rule.Result result = rule.apply(match.value(), match.captures(), ruleContext(context));
        return !result.isEmpty();
    }

    private boolean exploreChildren(int group, Context context, Matcher matcher)
    {
        boolean progress = false;

        PlanNode expression = context.memo.getNode(group);
        OptTrace.begin(context.session.getOptTrace(), "exploreChildren : group %s , node id %s , %s",
                group, expression.getId().getId(), expression.getClass().getSimpleName());
        for (PlanNode child : expression.getSources()) {
            checkState(child instanceof GroupReference, "Expected child to be a group reference. Found: " + child.getClass().getName());

            if (exploreGroup(((GroupReference) child).getGroupId(), context, matcher)) {
                progress = true;
            }
        }

        OptTrace.end(context.session.getOptTrace(), "exploreChildren : group %s , node id %s , %s , progress ? %s",
                group, expression.getId().getId(), expression.getClass().getSimpleName(), progress ? "true" : "false");

        return progress;
    }

    private Rule.Context ruleContext(Context context)
    {
        return new Rule.Context()
        {
            @Override
            public Lookup getLookup()
            {
                return context.lookup;
            }

            @Override
            public PlanNodeIdAllocator getIdAllocator()
            {
                return context.idAllocator;
            }

            @Override
            public VariableAllocator getVariableAllocator()
            {
                return context.variableAllocator;
            }

            @Override
            public Session getSession()
            {
                return context.session;
            }

            @Override
            public StatsProvider getStatsProvider()
            {
                return context.statsProvider;
            }

            @Override
            public CostProvider getCostProvider()
            {
                return context.costProvider;
            }

            @Override
            public void checkTimeoutNotExhausted()
            {
                context.checkTimeoutNotExhausted();
            }

            @Override
            public WarningCollector getWarningCollector()
            {
                return context.warningCollector;
            }

            @Override
            public Optional<LogicalPropertiesProvider> getLogicalPropertiesProvider()
            {
                return logicalPropertiesProvider;
            }

            @Override
            public Memo getMemo()
            {
                return context.memo;
            }
        };
    }

    private static class RuleTriggered
    {
        private final String rule;
        private final Optional<String> oldNode;
        private final Optional<String> newNode;

        public RuleTriggered(String rule, Optional<String> oldNode, Optional<String> newNode)
        {
            this.rule = requireNonNull(rule, "rule is null");
            this.oldNode = requireNonNull(oldNode, "oldNode is null");
            this.newNode = requireNonNull(newNode, "newNode is null");
        }

        public String getRule()
        {
            return rule;
        }

        public Optional<String> getOldNode()
        {
            return oldNode;
        }

        public Optional<String> getNewNode()
        {
            return newNode;
        }
    }

    private static class Context
    {
        private final Memo memo;
        private final Lookup lookup;
        private final PlanNodeIdAllocator idAllocator;
        private final VariableAllocator variableAllocator;
        private final long startTimeInNanos;
        private final long timeoutInMilliseconds;
        private final Session session;
        private final WarningCollector warningCollector;
        private final CostProvider costProvider;
        private final StatsProvider statsProvider;
        private final List<RuleTriggered> rulesTriggered;
        private final Set<String> rulesApplicable;
        private final Metadata metadata;
        private final TypeProvider types;

        public Context(
                Memo memo,
                Lookup lookup,
                PlanNodeIdAllocator idAllocator,
                VariableAllocator variableAllocator,
                long startTimeInNanos,
                long timeoutInMilliseconds,
                Session session,
                WarningCollector warningCollector,
                CostProvider costProvider,
                StatsProvider statsProvider,
                Metadata metadata,
                TypeProvider types)
        {
            checkArgument(timeoutInMilliseconds >= 0, "Timeout has to be a non-negative number [milliseconds]");

            this.memo = memo;
            this.lookup = lookup;
            this.idAllocator = idAllocator;
            this.variableAllocator = variableAllocator;
            this.startTimeInNanos = startTimeInNanos;
            this.timeoutInMilliseconds = timeoutInMilliseconds;
            this.session = session;
            this.warningCollector = warningCollector;
            this.costProvider = costProvider;
            this.statsProvider = statsProvider;
            this.metadata = metadata;
            this.types = types;
            this.rulesTriggered = new ArrayList<>();
            this.rulesApplicable = new HashSet<>();
        }

        public void checkTimeoutNotExhausted()
        {
            if ((NANOSECONDS.toMillis(System.nanoTime() - startTimeInNanos)) >= timeoutInMilliseconds) {
                throw new PrestoException(OPTIMIZER_TIMEOUT, format("The optimizer exhausted the time limit of %d ms", timeoutInMilliseconds));
            }
        }

        public void addRulesTriggered(String rule, PlanNode oldNode, PlanNode newNode)
        {
            Optional<String> before = Optional.empty();
            Optional<String> after = Optional.empty();

            if (SystemSessionProperties.isVerboseOptimizerResults(session, rule)) {
                before = Optional.of(PlannerUtils.getPlanString(oldNode, session, types, metadata, false));
                after = Optional.of(PlannerUtils.getPlanString(newNode, session, types, metadata, false));
            }

            rulesTriggered.add(new RuleTriggered(rule, before, after));
        }

        public void addRulesApplicable(String rule)
        {
            rulesApplicable.add(rule);
        }

        public void collectOptimizerInformation()
        {
            rulesTriggered.stream().map(x -> x.getRule()).distinct().forEach(rule -> session.getOptimizerInformationCollector().addInformation(new PlanOptimizerInformation(rule, true, Optional.empty(), Optional.empty())));
            if (SystemSessionProperties.isVerboseOptimizerResults(session)) {
                rulesTriggered.stream().filter(x -> x.getNewNode().isPresent()).forEach(x -> session.getOptimizerResultCollector().addOptimizerResult(x.getRule(), x.getOldNode().get(), x.getNewNode().get()));
            }
            rulesApplicable.forEach(x -> session.getOptimizerInformationCollector().addInformation(new PlanOptimizerInformation(x, false, Optional.of(true), Optional.empty())));
        }

        public void allocOptTrace(String dirPath)
        {
            if (session != null && isEnableOptimizerTrace(session)) {
                if (!(session.getOptTrace().isPresent())) {
                    session.setOptTrace(Optional.of(new OptTrace(dirPath, null, session, null, null, lookup, memo,
                            costProvider, statsProvider)));
                }
                else {
                    session.getOptTrace().ifPresent(optTrace -> optTrace.reinitialize(lookup, memo, costProvider, statsProvider));
                }
            }
        }
    }
}
