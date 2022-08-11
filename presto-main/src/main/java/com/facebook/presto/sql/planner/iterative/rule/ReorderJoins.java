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

package com.facebook.presto.sql.planner.iterative.rule;

import com.facebook.airlift.log.Logger;
import com.facebook.presto.Session;
import com.facebook.presto.cost.CostComparator;
import com.facebook.presto.cost.CostProvider;
import com.facebook.presto.cost.PlanCostEstimate;
import com.facebook.presto.cost.PlanNodeStatsEstimate;
import com.facebook.presto.expressions.LogicalRowExpressions;
import com.facebook.presto.matching.Captures;
import com.facebook.presto.matching.Pattern;
import com.facebook.presto.metadata.Metadata;
import com.facebook.presto.spi.VariableAllocator;
import com.facebook.presto.spi.plan.FilterNode;
import com.facebook.presto.spi.plan.PlanNode;
import com.facebook.presto.spi.plan.PlanNodeId;
import com.facebook.presto.spi.plan.PlanNodeIdAllocator;
import com.facebook.presto.spi.relation.CallExpression;
import com.facebook.presto.spi.relation.DeterminismEvaluator;
import com.facebook.presto.spi.relation.RowExpression;
import com.facebook.presto.spi.relation.VariableReferenceExpression;
import com.facebook.presto.sql.analyzer.FeaturesConfig.JoinDistributionType;
import com.facebook.presto.sql.planner.CanonicalJoinNode;
import com.facebook.presto.sql.planner.EqualityInference;
import com.facebook.presto.sql.planner.OptTrace;
import com.facebook.presto.sql.planner.OptTrace.Pair;
import com.facebook.presto.sql.planner.VariablesExtractor;
import com.facebook.presto.sql.planner.iterative.Lookup;
import com.facebook.presto.sql.planner.iterative.Rule;
import com.facebook.presto.sql.planner.optimizations.joins.JoinGraph;
import com.facebook.presto.sql.planner.plan.JoinNode;
import com.facebook.presto.sql.planner.plan.JoinNode.DistributionType;
import com.facebook.presto.sql.planner.plan.JoinNode.EquiJoinClause;
import com.facebook.presto.sql.relational.FunctionResolution;
import com.facebook.presto.sql.relational.RowExpressionDeterminismEvaluator;
import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.Predicate;
import com.google.common.base.VerifyException;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Ordering;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import static com.facebook.presto.SystemSessionProperties.getJoinDistributionType;
import static com.facebook.presto.SystemSessionProperties.getJoinReorderingStrategy;
import static com.facebook.presto.SystemSessionProperties.getMaxReorderedJoins;
import static com.facebook.presto.common.function.OperatorType.EQUAL;
import static com.facebook.presto.expressions.LogicalRowExpressions.TRUE_CONSTANT;
import static com.facebook.presto.expressions.LogicalRowExpressions.and;
import static com.facebook.presto.expressions.LogicalRowExpressions.extractConjuncts;
import static com.facebook.presto.sql.analyzer.FeaturesConfig.JoinReorderingStrategy.AUTOMATIC;
import static com.facebook.presto.sql.planner.EqualityInference.createEqualityInference;
import static com.facebook.presto.sql.planner.iterative.rule.DetermineJoinDistributionType.isBelowMaxBroadcastSize;
import static com.facebook.presto.sql.planner.iterative.rule.ReorderJoins.JoinEnumerationResult.INFINITE_COST_RESULT;
import static com.facebook.presto.sql.planner.iterative.rule.ReorderJoins.JoinEnumerationResult.UNKNOWN_COST_RESULT;
import static com.facebook.presto.sql.planner.iterative.rule.ReorderJoins.MultiJoinNode.toMultiJoinNode;
import static com.facebook.presto.sql.planner.optimizations.JoinNodeUtils.toRowExpression;
import static com.facebook.presto.sql.planner.optimizations.QueryCardinalityUtil.isAtMostScalar;
import static com.facebook.presto.sql.planner.plan.JoinNode.DistributionType.PARTITIONED;
import static com.facebook.presto.sql.planner.plan.JoinNode.DistributionType.REPLICATED;
import static com.facebook.presto.sql.planner.plan.JoinNode.Type.INNER;
import static com.facebook.presto.sql.planner.plan.Patterns.join;
import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static com.google.common.base.Predicates.in;
import static com.google.common.base.Verify.verify;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static com.google.common.collect.ImmutableSet.toImmutableSet;
import static com.google.common.collect.Iterables.getOnlyElement;
import static com.google.common.collect.Sets.powerSet;
import static java.util.Objects.requireNonNull;
import static java.util.stream.Collectors.toCollection;

public class ReorderJoins
        implements Rule<JoinNode>
{
    private static final Logger log = Logger.get(ReorderJoins.class);

    // We check that join distribution type is absent because we only want
    // to do this transformation once (reordered joins will have distribution type already set).
    private final Pattern<JoinNode> joinNodePattern;

    private final CostComparator costComparator;
    private final Metadata metadata;
    private final FunctionResolution functionResolution;
    private final DeterminismEvaluator determinismEvaluator;

    public ReorderJoins(CostComparator costComparator, Metadata metadata)
    {
        this.costComparator = requireNonNull(costComparator, "costComparator is null");
        this.metadata = requireNonNull(metadata, "metadata is null");
        this.functionResolution = new FunctionResolution(metadata.getFunctionAndTypeManager().getFunctionAndTypeResolver());
        this.determinismEvaluator = new RowExpressionDeterminismEvaluator(metadata.getFunctionAndTypeManager());

        this.joinNodePattern = join().matching(
                joinNode -> !joinNode.getDistributionType().isPresent()
                        && joinNode.getType() == INNER
                        && determinismEvaluator.isDeterministic(joinNode.getFilter().orElse(TRUE_CONSTANT)));
    }

    @Override
    public Pattern<JoinNode> getPattern()
    {
        return joinNodePattern;
    }

    @Override
    public boolean isEnabled(Session session)
    {
        return getJoinReorderingStrategy(session) == AUTOMATIC;
    }

    @Override
    public Result apply(JoinNode joinNode, Captures captures, Context context)
    {
        OptTrace.trace(context.getOptTrace(), joinNode, 0, "ReorderJoins:apply initial join node :");

        int maxReorderedJoins;
        if (OptTrace.joinConstraintsPresent(context.getOptTrace())) {
            OptTrace optTrace = context.getOptTrace().get();
            maxReorderedJoins = optTrace.getTableScanCnt(joinNode);
        }
        else {
            maxReorderedJoins = getMaxReorderedJoins(context.getSession());
        }

        MultiJoinNode multiJoinNode = toMultiJoinNode(joinNode, context.getLookup(), maxReorderedJoins, functionResolution, determinismEvaluator);

        JoinEnumerator joinEnumerator = new JoinEnumerator(
                costComparator,
                multiJoinNode.getFilter(),
                context,
                determinismEvaluator,
                functionResolution,
                metadata);

        List<JoinGraph> joinGraphList = JoinGraph.buildFromWithLookup(joinNode, context.getLookup());

        if (context.getOptTrace().isPresent()) {
            int cnt = 0;
            OptTrace optTrace = context.getOptTrace().get();
            optTrace.msg("All join graphs :", true);
            optTrace.incrIndent(1);
            for (JoinGraph joinGraph : joinGraphList) {
                optTrace.msg("Join graph %d :", true, cnt);
                optTrace.incrIndent(1);
                optTrace.msgNoIndent("%s", true, joinGraph.toStringWithNames(optTrace.getIndent(), context.getLookup(), joinGraphList, joinNode));
                optTrace.decrIndent(1);
                ++cnt;
            }
            optTrace.decrIndent(1);
        }

        JoinEnumerationResult result = joinEnumerator.chooseJoinOrder(multiJoinNode.getSources(), multiJoinNode.getOutputVariables());

        OptTrace.trace(context.getOptTrace(), multiJoinNode.getSources(), 0, "Join Sources :");
        OptTrace.traceEnumeratedJoins(context.getOptTrace(), joinNode, context.getCostProvider(), context.getStatsProvider(), 0, "All enumerated joins :");
        if (result.getPlanNode().isPresent()) {
            OptTrace.traceJoinConstraint(context.getOptTrace(), result.getPlanNode().get(), 0, "Final join constraint :");
            result.trace(context.getOptTrace(), 0, "Enumerator chosen join order :", false);
        }
        else {
            OptTrace.msg(context.getOptTrace(), "Final join constraint : <empty>", true);
        }

        if (!result.getPlanNode().isPresent()) {
            OptTrace.msg(context.getOptTrace(), "result is empty", true);
            return Result.empty();
        }

        return Result.ofPlanNode(result.getPlanNode().get());
    }

    @VisibleForTesting
    static class JoinEnumerator
    {
        private final Session session;
        private final CostProvider costProvider;
        // Using Ordering to facilitate rule determinism
        private final Ordering<JoinEnumerationResult> resultComparator;
        private final PlanNodeIdAllocator idAllocator;
        private final Metadata metadata;
        private final RowExpression allFilter;
        private final EqualityInference allFilterInference;
        private final LogicalRowExpressions logicalRowExpressions;
        private final Lookup lookup;
        private final Context context;

        private final Map<Set<PlanNode>, JoinEnumerationResult> memo = new HashMap<>();

        @VisibleForTesting
        JoinEnumerator(CostComparator costComparator, RowExpression filter, Context context, DeterminismEvaluator determinismEvaluator, FunctionResolution functionResolution, Metadata metadata)
        {
            this.context = requireNonNull(context);
            this.session = requireNonNull(context.getSession(), "session is null");
            this.costProvider = requireNonNull(context.getCostProvider(), "costProvider is null");
            this.resultComparator = costComparator.forSession(session).onResultOf(result -> result.cost);
            this.idAllocator = requireNonNull(context.getIdAllocator(), "idAllocator is null");
            this.allFilter = requireNonNull(filter, "filter is null");
            this.lookup = requireNonNull(context.getLookup(), "lookup is null");

            this.metadata = requireNonNull(metadata, "metadata is null");
            this.allFilterInference = createEqualityInference(metadata, filter);
            this.logicalRowExpressions = new LogicalRowExpressions(determinismEvaluator, functionResolution, metadata.getFunctionAndTypeManager());
        }

        private static void trace(Optional<OptTrace> optTraceParam, JoinEnumerationResult result,
                int indentCnt, String msgString, Object... args)
        {
            if (optTraceParam.isPresent()) {
                result.trace(optTraceParam, indentCnt, msgString, true);
            }
        }

        private static void trace(Optional<OptTrace> optTraceParam, List<JoinEnumerationResult> results,
                int indentCnt, String msgString, Object... args)
        {
            if (optTraceParam.isPresent()) {
                optTraceParam.ifPresent(optTrace -> optTrace.incrIndent(indentCnt));
                if (msgString != null) {
                    optTraceParam.ifPresent(optTrace -> optTrace.msg(msgString, true, args));
                    optTraceParam.ifPresent(optTrace -> optTrace.incrIndent(1));
                }

                if (!results.isEmpty()) {
                    int cnt = 0;
                    for (JoinEnumerationResult nextResult : results) {
                        nextResult.trace(optTraceParam, 0, "Result %d :", true, cnt);
                        ++cnt;
                    }
                }
                else {
                    optTraceParam.ifPresent(optTrace -> optTrace.msg("Empty.", true, args));
                }

                if (msgString != null) {
                    optTraceParam.ifPresent(optTrace -> optTrace.decrIndent(1));
                }

                optTraceParam.ifPresent(optTrace -> optTrace.decrIndent(indentCnt));
            }
        }

        private JoinEnumerationResult chooseJoinOrder(LinkedHashSet<PlanNode> sources, List<VariableReferenceExpression> outputVariables)
        {
            context.checkTimeoutNotExhausted();
            OptTrace.begin(context.getOptTrace(), "chooseJoinOrder");
            OptTrace.trace(context.getOptTrace(), sources, 0, "Join Sources :");

            Set<PlanNode> multiJoinKey = ImmutableSet.copyOf(sources);
            JoinEnumerationResult bestResult = memo.get(multiJoinKey);

            if (bestResult == null) {
                OptTrace.msg(context.getOptTrace(), "No result in memo. Will enumerate.", true);
                checkState(sources.size() > 1, "sources size is less than or equal to one");
                ImmutableList.Builder<JoinEnumerationResult> resultBuilder = ImmutableList.builder();
                Set<Set<Integer>> partitions = generatePartitions(sources.size());
                for (Set<Integer> partition : partitions) {
                    OptTrace.begin(context.getOptTrace(), "createJoinAccordingToPartitioning");
                    OptTrace.trace(context.getOptTrace(), partition, "Next partition %d-way : ", sources.size());

                    JoinEnumerationResult result = createJoinAccordingToPartitioning(sources, outputVariables, partition);

                    OptTrace.end(context.getOptTrace(), "createJoinAccordingToPartitioning");
                    result.trace(context.getOptTrace(), 0, "Next enumerated join :", true);

                    if (result.equals(UNKNOWN_COST_RESULT)) {
                        memo.put(multiJoinKey, result);
                        OptTrace.end(context.getOptTrace(), "chooseJoinOrder");
                        return result;
                    }
                    if (!result.equals(INFINITE_COST_RESULT)) {
                        resultBuilder.add(result);
                    }
                }

                List<JoinEnumerationResult> results = resultBuilder.build();

                if (this.session.getOptTrace().isPresent() && results.size() > 1) {
                    OptTrace optTrace = this.session.getOptTrace().get();
                    JoinEnumerationResult minResult = resultComparator.min(results);

                    for (JoinEnumerationResult currentResult : results) {
                        if (currentResult != minResult) {
                            optTrace.addPrunedJoinId(optTrace.getJoinId(currentResult.getPlanNode().get()), OptTrace.PruneReason.COST);
                        }
                    }
                }

                trace(context.getOptTrace(), results, 0, "All results :");

                if (results.isEmpty()) {
                    memo.put(multiJoinKey, INFINITE_COST_RESULT);
                    OptTrace.end(context.getOptTrace(), "chooseJoinOrder");
                    return INFINITE_COST_RESULT;
                }

                bestResult = resultComparator.min(results);
                memo.put(multiJoinKey, bestResult);
            }
            else {
                OptTrace.msg(context.getOptTrace(), "Found best result in memo.", true);
            }

            bestResult.trace(context.getOptTrace(), 1, "Best result :", true);

            bestResult.planNode.ifPresent((planNode) -> log.debug("Least cost join was: %s", planNode));
            OptTrace.end(context.getOptTrace(), "chooseJoinOrder");
            return bestResult;
        }

        /**
         * This method generates all the ways of dividing totalNodes into two sets
         * each containing at least one node. It will generate one set for each
         * possible partitioning. The other partition is implied in the absent values.
         * In order not to generate the inverse of any set, we always include the 0th
         * node in our sets.
         *
         * @return A set of sets each of which defines a partitioning of totalNodes
         */
        @VisibleForTesting
        static Set<Set<Integer>> generatePartitions(int totalNodes)
        {
            checkArgument(totalNodes > 1, "totalNodes must be greater than 1");
            Set<Integer> numbers = IntStream.range(0, totalNodes)
                    .boxed()
                    .collect(toImmutableSet());
            return powerSet(numbers).stream()
                    .filter(subSet -> subSet.contains(0))
                    .filter(subSet -> subSet.size() < numbers.size())
                    .collect(toImmutableSet());
        }

        @VisibleForTesting
        JoinEnumerationResult createJoinAccordingToPartitioning(LinkedHashSet<PlanNode> sources, List<VariableReferenceExpression> outputVariables, Set<Integer> partitioning)
        {
            List<PlanNode> sourceList = ImmutableList.copyOf(sources);
            LinkedHashSet<PlanNode> leftSources = partitioning.stream()
                    .map(sourceList::get)
                    .collect(toCollection(LinkedHashSet::new));
            LinkedHashSet<PlanNode> rightSources = sources.stream()
                    .filter(source -> !leftSources.contains(source))
                    .collect(toCollection(LinkedHashSet::new));

            OptTrace.trace(context.getOptTrace(), sources, 1, "Sources %d-way :", sources.size());
            OptTrace.trace(context.getOptTrace(), leftSources, 1, "Left Sources %d-way :", leftSources.size());
            OptTrace.trace(context.getOptTrace(), rightSources, 1, "Right Sources %d-way :", rightSources.size());

            return createJoin(leftSources, rightSources, outputVariables);
        }

        private JoinEnumerationResult createJoin(LinkedHashSet<PlanNode> leftSources, LinkedHashSet<PlanNode> rightSources, List<VariableReferenceExpression> outputVariables)
        {
            Set<VariableReferenceExpression> leftVariables = leftSources.stream()
                    .flatMap(node -> node.getOutputVariables().stream())
                    .collect(toImmutableSet());
            Set<VariableReferenceExpression> rightVariables = rightSources.stream()
                    .flatMap(node -> node.getOutputVariables().stream())
                    .collect(toImmutableSet());

            List<RowExpression> joinPredicates = getJoinPredicates(leftVariables, rightVariables);
            List<EquiJoinClause> joinConditions = joinPredicates.stream()
                    .filter(JoinEnumerator::isJoinEqualityCondition)
                    .map(predicate -> toEquiJoinClause((CallExpression) predicate, leftVariables, context.getVariableAllocator()))
                    .collect(toImmutableList());
            if (joinConditions.isEmpty() && !OptTrace.joinConstraintsPresent(context.getOptTrace())) {
                OptTrace.msg(context.getOptTrace(), "No join conditions and no join constraints. Join cost is infinite.", true);
                return INFINITE_COST_RESULT;
            }
            List<RowExpression> joinFilters = joinPredicates.stream()
                    .filter(predicate -> !isJoinEqualityCondition(predicate))
                    .collect(toImmutableList());

            Set<VariableReferenceExpression> requiredJoinVariables = ImmutableSet.<VariableReferenceExpression>builder()
                    .addAll(outputVariables)
                    .addAll(VariablesExtractor.extractUnique(joinPredicates))
                    .build();

            JoinEnumerationResult leftResult = getJoinSource(
                    leftSources,
                    requiredJoinVariables.stream()
                            .filter(leftVariables::contains)
                            .collect(toImmutableList()));
            leftResult.trace(context.getOptTrace(), 0, "Left result :", true);

            boolean leftSatisfiesConstraint = false;
            if (context.getOptTrace().isPresent() && leftResult.getPlanNode().isPresent()) {
                leftSatisfiesConstraint = OptTrace.satisfiesAnyJoinConstraint(session.getOptTrace(), leftResult.getPlanNode().get());
            }

            if (leftResult.equals(UNKNOWN_COST_RESULT) && !leftSatisfiesConstraint) {
                return UNKNOWN_COST_RESULT;
            }
            if (leftResult.equals(INFINITE_COST_RESULT) && !leftSatisfiesConstraint) {
                return INFINITE_COST_RESULT;
            }

            PlanNode left = leftResult.planNode.orElseThrow(() -> new VerifyException("Plan node is not present"));

            JoinEnumerationResult rightResult = getJoinSource(
                    rightSources,
                    requiredJoinVariables.stream()
                            .filter(rightVariables::contains)
                            .collect(toImmutableList()));
            rightResult.trace(context.getOptTrace(), 0, "Right result :", true);

            boolean rightSatisfiesConstraint = false;
            if (context.getOptTrace().isPresent() && rightResult.getPlanNode().isPresent()) {
                rightSatisfiesConstraint = OptTrace.satisfiesAnyJoinConstraint(session.getOptTrace(), rightResult.getPlanNode().get());
            }
            if (rightResult.equals(UNKNOWN_COST_RESULT) && !rightSatisfiesConstraint) {
                return UNKNOWN_COST_RESULT;
            }
            if (rightResult.equals(INFINITE_COST_RESULT) && !rightSatisfiesConstraint) {
                return INFINITE_COST_RESULT;
            }

            PlanNode right = rightResult.planNode.orElseThrow(() -> new VerifyException("Plan node is not present"));

            // sort output variables so that the left input variables are first
            List<VariableReferenceExpression> sortedOutputVariables = Stream.concat(left.getOutputVariables().stream(), right.getOutputVariables().stream())
                    .filter(outputVariables::contains)
                    .collect(toImmutableList());

            return setJoinNodeProperties(new JoinNode(
                    left.getSourceLocation(),
                    idAllocator.getNextId(),
                    INNER,
                    left,
                    right,
                    joinConditions,
                    sortedOutputVariables,
                    joinFilters.isEmpty() ? Optional.empty() : Optional.of(and(joinFilters)),
                    Optional.empty(),
                    Optional.empty(),
                    Optional.empty(),
                    ImmutableMap.of()));
        }

        private List<RowExpression> getJoinPredicates(Set<VariableReferenceExpression> leftVariables, Set<VariableReferenceExpression> rightVariables)
        {
            ImmutableList.Builder<RowExpression> joinPredicatesBuilder = ImmutableList.builder();
            // This takes all conjuncts that were part of allFilters that
            // could not be used for equality inference.
            // If they use both the left and right variables, we add them to the list of joinPredicates
            EqualityInference.Builder builder = new EqualityInference.Builder(metadata);
            StreamSupport.stream(builder.nonInferableConjuncts(allFilter).spliterator(), false)
                    .map(conjunct -> allFilterInference.rewriteExpression(
                            conjunct,
                            variable -> leftVariables.contains(variable) || rightVariables.contains(variable)))
                    .filter(Objects::nonNull)
                    // filter expressions that contain only left or right variables
                    .filter(conjunct -> allFilterInference.rewriteExpression(conjunct, leftVariables::contains) == null)
                    .filter(conjunct -> allFilterInference.rewriteExpression(conjunct, rightVariables::contains) == null)
                    .forEach(joinPredicatesBuilder::add);

            // create equality inference on available variables
            // TODO: make generateEqualitiesPartitionedBy take left and right scope
            List<RowExpression> joinEqualities = allFilterInference.generateEqualitiesPartitionedBy(
                    variable -> leftVariables.contains(variable) || rightVariables.contains(variable)).getScopeEqualities();
            EqualityInference joinInference = createEqualityInference(metadata, joinEqualities.toArray(new RowExpression[0]));
            joinPredicatesBuilder.addAll(joinInference.generateEqualitiesPartitionedBy(in(leftVariables)).getScopeStraddlingEqualities());

            return joinPredicatesBuilder.build();
        }

        private JoinEnumerationResult getJoinSource(LinkedHashSet<PlanNode> nodes, List<VariableReferenceExpression> outputVariables)
        {
            if (nodes.size() == 1) {
                PlanNode planNode = getOnlyElement(nodes);
                ImmutableList.Builder<RowExpression> predicates = ImmutableList.builder();
                predicates.addAll(allFilterInference.generateEqualitiesPartitionedBy(outputVariables::contains).getScopeEqualities());
                EqualityInference.Builder builder = new EqualityInference.Builder(metadata);
                StreamSupport.stream(builder.nonInferableConjuncts(allFilter).spliterator(), false)
                        .map(conjunct -> allFilterInference.rewriteExpression(conjunct, outputVariables::contains))
                        .filter(Objects::nonNull)
                        .forEach(predicates::add);
                RowExpression filter = logicalRowExpressions.combineConjuncts(predicates.build());
                if (!TRUE_CONSTANT.equals(filter)) {
                    planNode = new FilterNode(planNode.getSourceLocation(), idAllocator.getNextId(), planNode, filter);
                }
                return createJoinEnumerationResult(planNode);
            }
            return chooseJoinOrder(nodes, outputVariables);
        }

        private static boolean isJoinEqualityCondition(RowExpression expression)
        {
            return expression instanceof CallExpression
                    && ((CallExpression) expression).getDisplayName().equals(EQUAL.getFunctionName().getObjectName())
                    && ((CallExpression) expression).getArguments().size() == 2
                    && ((CallExpression) expression).getArguments().get(0) instanceof VariableReferenceExpression
                    && ((CallExpression) expression).getArguments().get(1) instanceof VariableReferenceExpression;
        }

        private static EquiJoinClause toEquiJoinClause(CallExpression equality, Set<VariableReferenceExpression> leftVariables, VariableAllocator variableAllocator)
        {
            checkArgument(equality.getArguments().size() == 2, "Unexpected number of arguments in binary operator equals");
            VariableReferenceExpression leftVariable = (VariableReferenceExpression) equality.getArguments().get(0);
            VariableReferenceExpression rightVariable = (VariableReferenceExpression) equality.getArguments().get(1);
            EquiJoinClause equiJoinClause = new EquiJoinClause(leftVariable, rightVariable);
            return leftVariables.contains(leftVariable) ? equiJoinClause : equiJoinClause.flip();
        }

        private JoinEnumerationResult setJoinNodeProperties(JoinNode joinNode)
        {
            OptTrace.begin(this.session.getOptTrace(), "setJoinNodeProperties");

            // TODO avoid stat (but not cost) recalculation for all considered (distribution,flip) pairs, since resulting relation is the same in all case
            if (isAtMostScalar(joinNode.getRight(), lookup)) {
                OptTrace.msg(this.session.getOptTrace(), "Right is scalar so distribution is REPLICATED", true);
                OptTrace.end(this.session.getOptTrace(), "setJoinNodeProperties");
                return createJoinEnumerationResult(joinNode.withDistributionType(REPLICATED));
            }
            if (isAtMostScalar(joinNode.getLeft(), lookup)) {
                OptTrace.msg(this.session.getOptTrace(), "Left is scalar so distribution is REPLICATED", true);
                OptTrace.end(this.session.getOptTrace(), "setJoinNodeProperties");
                return createJoinEnumerationResult(joinNode.flipChildren().withDistributionType(REPLICATED));
            }
            List<JoinEnumerationResult> possibleJoinNodes = getPossibleJoinNodes(joinNode, getJoinDistributionType(session));
            verify(!possibleJoinNodes.isEmpty(), "possibleJoinNodes is empty");

            trace(context.getOptTrace(), possibleJoinNodes, 1, "Possible joins :");

            if (possibleJoinNodes.stream().anyMatch(UNKNOWN_COST_RESULT::equals)) {
                OptTrace.msg(this.session.getOptTrace(), "Result : <unknown cost>", true);
                OptTrace.end(this.session.getOptTrace(), "setJoinNodeProperties");
                return UNKNOWN_COST_RESULT;
            }

            if (this.session.getOptTrace().isPresent() && possibleJoinNodes.size() > 1) {
                OptTrace optTrace = this.session.getOptTrace().get();
                JoinEnumerationResult minResult = resultComparator.min(possibleJoinNodes);
                optTrace.incrIndent(1);
                for (JoinEnumerationResult currentResult : possibleJoinNodes) {
                    if (currentResult != minResult) {
                        currentResult.trace(this.session.getOptTrace(), 1, "Next enumerated join (** PRUNED BY COST **) : :",
                                true);

                        if (currentResult.getPlanNode().isPresent()) {
                            optTrace.addPrunedJoinId(optTrace.getJoinId(currentResult.getPlanNode().get()), OptTrace.PruneReason.COST);
                        }
                    }
                }

                optTrace.decrIndent(1);

                minResult.trace(this.session.getOptTrace(), 1, "Result :", true);
                OptTrace.end(this.session.getOptTrace(), "setJoinNodeProperties");
            }

            return resultComparator.min(possibleJoinNodes);
        }

        private List<JoinEnumerationResult> getPossibleJoinNodes(JoinNode joinNode, JoinDistributionType distributionType)
        {
            checkArgument(joinNode.getType() == INNER, "unexpected join node type: %s", joinNode.getType());

            if (joinNode.getCriteria().isEmpty() && joinNode.getType() == INNER) {
                boolean joinOk = false;

                if (OptTrace.joinConstraintsPresent(context.getOptTrace())) {
                    if (OptTrace.satisfiesAnyJoinConstraint(context.getOptTrace(), joinNode, true)) {
                        joinOk = true;
                    }
                    else if (OptTrace.satisfiesAnyJoinConstraint(context.getOptTrace(), joinNode.flipChildren(), true)) {
                        joinOk = true;
                    }
                }

                if (!joinOk) {
                    OptTrace.msg(context.getOptTrace(), "No join conditions or matching constraint. Join cost is infinite.", true);
                    List<JoinEnumerationResult> result = ImmutableList.of(INFINITE_COST_RESULT);
                    return result;
                }
            }

            if (joinNode.isCrossJoin()) {
                return getPossibleJoinNodes(joinNode, REPLICATED);
            }

            switch (distributionType) {
                case PARTITIONED:
                    return getPossibleJoinNodes(joinNode, PARTITIONED);
                case BROADCAST:
                    return getPossibleJoinNodes(joinNode, REPLICATED);
                case AUTOMATIC:
                    ImmutableList.Builder<JoinEnumerationResult> result = ImmutableList.builder();
                    result.addAll(getPossibleJoinNodes(joinNode, PARTITIONED));
                    result.addAll(getPossibleJoinNodes(joinNode, REPLICATED, node -> isBelowMaxBroadcastSize(node, context)));
                    return result.build();
                default:
                    throw new IllegalArgumentException("unexpected join distribution type: " + distributionType);
            }
        }

        private List<JoinEnumerationResult> getPossibleJoinNodes(JoinNode joinNode, DistributionType distributionType)
        {
            return getPossibleJoinNodes(joinNode, distributionType, (node) -> true);
        }

        private List<JoinEnumerationResult> getPossibleJoinNodes(JoinNode joinNode, DistributionType distributionType, Predicate<JoinNode> isAllowed)
        {
            List<JoinNode> nodes = ImmutableList.of(
                    joinNode.withDistributionType(distributionType),
                    joinNode.flipChildren().withDistributionType(distributionType));
            return nodes.stream().filter(isAllowed).map(this::createJoinEnumerationResult).collect(toImmutableList());
        }

        private JoinEnumerationResult createJoinEnumerationResult(PlanNode planNode)
        {
            OptTrace.addEnumeratedJoin(context.getOptTrace(), planNode);

            JoinEnumerationResult result;
            if (!OptTrace.valid(context.getOptTrace(), planNode)) {
                //result = new JoinEnumerationResult(Optional.of(planNode), PlanCostEstimate.infinite());
                result = INFINITE_COST_RESULT;
            }
            else {
                result = JoinEnumerationResult.createJoinEnumerationResult(Optional.of(planNode), costProvider.getCost(planNode));
                trace(context.getOptTrace(), result, 0, "Next valid result :");
            }

            return result;
        }
    }

    /**
     * This class represents a set of inner joins that can be executed in any order.
     */
    @VisibleForTesting
    static class MultiJoinNode
    {
        // Use a linked hash set to ensure optimizer is deterministic
        private final CanonicalJoinNode node;

        public MultiJoinNode(LinkedHashSet<PlanNode> sources, RowExpression filter, List<VariableReferenceExpression> outputVariables)
        {
            checkArgument(sources.size() > 1, "sources size is <= 1");

            requireNonNull(sources, "sources is null");
            requireNonNull(filter, "filter is null");
            requireNonNull(outputVariables, "outputVariables is null");
            // Plan node id doesn't matter here as we don't use this in planner
            this.node = new CanonicalJoinNode(
                    new PlanNodeId(""),
                    sources.stream().collect(toImmutableList()),
                    INNER,
                    ImmutableSet.of(),
                    ImmutableSet.of(filter),
                    outputVariables);

            List<VariableReferenceExpression> inputVariables = sources.stream().flatMap(source -> source.getOutputVariables().stream()).collect(toImmutableList());
            checkArgument(inputVariables.containsAll(outputVariables), "inputs do not contain all output variables");
        }

        public RowExpression getFilter()
        {
            return node.getFilters().stream().findAny().get();
        }

        public LinkedHashSet<PlanNode> getSources()
        {
            return new LinkedHashSet<>(node.getSources());
        }

        public List<VariableReferenceExpression> getOutputVariables()
        {
            return node.getOutputVariables();
        }

        public static Builder builder()
        {
            return new Builder();
        }

        @Override
        public int hashCode()
        {
            return Objects.hash(getSources(), ImmutableSet.copyOf(extractConjuncts(getFilter())), getOutputVariables());
        }

        @Override
        public boolean equals(Object obj)
        {
            if (!(obj instanceof MultiJoinNode)) {
                return false;
            }

            MultiJoinNode other = (MultiJoinNode) obj;
            return getSources().equals(other.getSources())
                    && ImmutableSet.copyOf(extractConjuncts(getFilter())).equals(ImmutableSet.copyOf(extractConjuncts(other.getFilter())))
                    && getOutputVariables().equals(other.getOutputVariables());
        }

        static MultiJoinNode toMultiJoinNode(JoinNode joinNode, Lookup lookup, int joinLimit, FunctionResolution functionResolution, DeterminismEvaluator determinismEvaluator)
        {
            // the number of sources is the number of joins + 1
            return new JoinNodeFlattener(joinNode, lookup, joinLimit + 1, functionResolution, determinismEvaluator).toMultiJoinNode();
        }

        private static class JoinNodeFlattener
        {
            private final LinkedHashSet<PlanNode> sources = new LinkedHashSet<>();
            private final List<RowExpression> filters = new ArrayList<>();
            private final List<VariableReferenceExpression> outputVariables;
            private final FunctionResolution functionResolution;
            private final DeterminismEvaluator determinismEvaluator;
            private final Lookup lookup;

            JoinNodeFlattener(JoinNode node, Lookup lookup, int sourceLimit, FunctionResolution functionResolution, DeterminismEvaluator determinismEvaluator)
            {
                requireNonNull(node, "node is null");
                checkState(node.getType() == INNER, "join type must be INNER");
                this.outputVariables = node.getOutputVariables();
                this.lookup = requireNonNull(lookup, "lookup is null");
                this.functionResolution = requireNonNull(functionResolution, "functionResolution is null");
                this.determinismEvaluator = requireNonNull(determinismEvaluator, "determinismEvaluator is null");
                flattenNode(node, sourceLimit);
            }

            private void flattenNode(PlanNode node, int limit)
            {
                PlanNode resolved = lookup.resolve(node);

                // (limit - 2) because you need to account for adding left and right side
                if (!(resolved instanceof JoinNode) || (sources.size() > (limit - 2))) {
                    sources.add(node);
                    return;
                }

                JoinNode joinNode = (JoinNode) resolved;
                if (joinNode.getType() != INNER || !determinismEvaluator.isDeterministic(joinNode.getFilter().orElse(TRUE_CONSTANT)) || joinNode.getDistributionType().isPresent()) {
                    sources.add(node);
                    return;
                }

                // we set the left limit to limit - 1 to account for the node on the right
                flattenNode(joinNode.getLeft(), limit - 1);
                flattenNode(joinNode.getRight(), limit);
                joinNode.getCriteria().stream()
                        .map(criteria -> toRowExpression(criteria, functionResolution))
                        .forEach(filters::add);
                joinNode.getFilter().ifPresent(filters::add);
            }

            MultiJoinNode toMultiJoinNode()
            {
                return new MultiJoinNode(sources, and(filters), outputVariables);
            }
        }

        static class Builder
        {
            private List<PlanNode> sources;
            private RowExpression filter;
            private List<VariableReferenceExpression> outputVariables;

            public Builder setSources(PlanNode... sources)
            {
                this.sources = ImmutableList.copyOf(sources);
                return this;
            }

            public Builder setFilter(RowExpression filter)
            {
                this.filter = filter;
                return this;
            }

            public Builder setOutputVariables(VariableReferenceExpression... outputVariables)
            {
                this.outputVariables = ImmutableList.copyOf(outputVariables);
                return this;
            }

            public MultiJoinNode build()
            {
                return new MultiJoinNode(new LinkedHashSet<>(sources), filter, outputVariables);
            }
        }
    }

    @VisibleForTesting
    static class JoinEnumerationResult
    {
        public static final JoinEnumerationResult UNKNOWN_COST_RESULT = new JoinEnumerationResult(Optional.empty(), PlanCostEstimate.unknown());
        public static final JoinEnumerationResult INFINITE_COST_RESULT = new JoinEnumerationResult(Optional.empty(), PlanCostEstimate.infinite());
        private final Optional<PlanNode> planNode;
        private final PlanCostEstimate cost;

        private JoinEnumerationResult(Optional<PlanNode> planNode, PlanCostEstimate cost)
        {
            this.planNode = requireNonNull(planNode, "planNode is null");
            this.cost = requireNonNull(cost, "cost is null");
            checkArgument((cost.hasUnknownComponents() || cost.equals(PlanCostEstimate.infinite())) && !planNode.isPresent()
                            || (!cost.hasUnknownComponents() || !cost.equals(PlanCostEstimate.infinite())) && planNode.isPresent(),
                    "planNode should be present if and only if cost is known");
        }

        public Optional<PlanNode> getPlanNode()
        {
            return planNode;
        }

        public PlanCostEstimate getCost()
        {
            return cost;
        }

        static JoinEnumerationResult createJoinEnumerationResult(Optional<PlanNode> planNode, PlanCostEstimate cost)
        {
            if (cost.hasUnknownComponents()) {
                return UNKNOWN_COST_RESULT;
            }
            if (cost.equals(PlanCostEstimate.infinite())) {
                return INFINITE_COST_RESULT;
            }
            return new JoinEnumerationResult(planNode, cost);
        }

        private void trace(Optional<OptTrace> optTraceParam, int indentCnt, String msgString, boolean brief, Object... args)
        {
            if (optTraceParam.isPresent()) {
                if (args != null) {
                    msgString = String.format(msgString, args);
                }

                OptTrace optTrace = optTraceParam.get();

                if (this.equals(INFINITE_COST_RESULT)) {
                    msgString = msgString + " (infinite cost)";
                    optTrace.msg(msgString, true);
                }
                else if (this.equals(UNKNOWN_COST_RESULT)) {
                    msgString = msgString + " (unknown cost)";
                    optTrace.msg(msgString, true);
                }
                else {
                    Optional<PlanNode> nextPlanNode = this.getPlanNode();

                    PlanNodeStatsEstimate stats = null;
                    if (nextPlanNode.isPresent()) {
                        PlanNode planNode = nextPlanNode.get();

                        Pair<String, String> joinStrings = optTrace.getJoinStrings(planNode);

                        requireNonNull(joinStrings, "join strings are null");
                        msgString = msgString + " (" + joinStrings.getKey() + " , join id " + optTrace.getJoinId(planNode) +
                                " , hash code " + joinStrings.getKey().hashCode() + ")";
                        optTrace.msg(msgString, true);
                        optTrace.incrIndent(1);

                        optTrace.msg("Constraint : %s", true, joinStrings.getValue());
                        optTrace.decrIndent(1);

                        if (!brief) {
                            optTrace.tracePlanNode(planNode, 1, "Plan :");
                        }

                        if (optTrace.statsProvider() != null) {
                            stats = optTrace.statsProvider().getStats(planNode);
                        }
                    }
                    else {
                        optTrace.incrIndent(indentCnt);
                        optTrace.msg("<no join present>", true);
                        optTrace.decrIndent(indentCnt);
                    }

                    optTrace.tracePlanCostEstimate(this.getCost(), 1, "Estimated cost :");

                    if (stats != null) {
                        optTrace.tracePlanNodeStatsEstimate(stats, 1, "Estimated stats :");
                    }
                }
            }
        }
    }
}
