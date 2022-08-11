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
package com.facebook.presto.sql.planner;

import com.facebook.presto.Session;
import com.facebook.presto.cost.CostProvider;
import com.facebook.presto.cost.PlanCostEstimate;
import com.facebook.presto.cost.PlanNodeStatsEstimate;
import com.facebook.presto.cost.StatsProvider;
import com.facebook.presto.metadata.Metadata;
import com.facebook.presto.server.BasicQueryInfo;
import com.facebook.presto.spi.PrestoException;
import com.facebook.presto.spi.SourceLocation;
import com.facebook.presto.spi.plan.AggregationNode;
import com.facebook.presto.spi.plan.Assignments;
import com.facebook.presto.spi.plan.FilterNode;
import com.facebook.presto.spi.plan.Ordering;
import com.facebook.presto.spi.plan.OrderingScheme;
import com.facebook.presto.spi.plan.PlanNode;
import com.facebook.presto.spi.plan.ProjectNode;
import com.facebook.presto.spi.plan.TableScanNode;
import com.facebook.presto.spi.plan.ValuesNode;
import com.facebook.presto.spi.relation.InSubqueryExpression;
import com.facebook.presto.spi.relation.RowExpression;
import com.facebook.presto.spi.relation.VariableReferenceExpression;
import com.facebook.presto.sql.analyzer.Analysis;
import com.facebook.presto.sql.parser.SqlParser;
import com.facebook.presto.sql.planner.iterative.GroupReference;
import com.facebook.presto.sql.planner.iterative.Lookup;
import com.facebook.presto.sql.planner.iterative.Memo;
import com.facebook.presto.sql.planner.optimizations.ActualProperties;
import com.facebook.presto.sql.planner.optimizations.JoinNodeUtils;
import com.facebook.presto.sql.planner.optimizations.PreferredProperties;
import com.facebook.presto.sql.planner.optimizations.PropertyDerivations;
import com.facebook.presto.sql.planner.plan.ApplyNode;
import com.facebook.presto.sql.planner.plan.ExchangeNode;
import com.facebook.presto.sql.planner.plan.InternalPlanVisitor;
import com.facebook.presto.sql.planner.plan.JoinNode;
import com.facebook.presto.sql.planner.plan.PlanFragmentId;
import com.facebook.presto.sql.planner.plan.RemoteSourceNode;
import com.facebook.presto.sql.planner.plan.SemiJoinNode;
import com.facebook.presto.sql.tree.AliasedRelation;
import com.facebook.presto.sql.tree.DefaultTraversalVisitor;
import com.facebook.presto.sql.tree.Expression;
import com.facebook.presto.sql.tree.Node;
import com.facebook.presto.sql.tree.NodeLocation;
import com.facebook.presto.sql.tree.Query;
import com.facebook.presto.sql.tree.Relation;
import com.facebook.presto.sql.tree.Table;
import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.common.base.Joiner;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import javax.annotation.Nullable;
import javax.annotation.concurrent.Immutable;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.facebook.presto.operator.scalar.MathFunctions.round;
import static com.facebook.presto.spi.StandardErrorCode.GENERIC_INTERNAL_ERROR;
import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static java.lang.String.format;
import static java.util.Arrays.stream;
import static java.util.Objects.requireNonNull;
import static java.util.stream.Collectors.toList;

public class OptTrace
{
    File file;
    FileWriter fileWriter;
    BufferedWriter bufferedWriter;
    int indent;
    int incrIndent;
    long uid;
    Lookup lookUp;
    Memo memo;
    Stack<Long> uidStack;
    BasicQueryInfo queryInfo;
    boolean outputQueryInfo;
    HashMap<String, Integer> traceIdMap;
    HashMap<String, Integer> joinIdMap;
    Integer minusOne;
    HashMap<PlanNode, Pair<String, String>> joinStringMap;
    int currentTraceId;
    int currentJoinId;
    ArrayList<JoinConstraintNode> planConstraints;
    ArrayList<JoinNode> enumeratedJoins;
    HashMap<Integer, PruneReason> prunedJoinIds;
    ArrayList<Integer> validUnderConstraintsJoinIds;
    boolean traceIdsAssigned;
    HashMap<String, PreferredProperties> planNodeIdToPreferredPropertiesMap;
    HashMap<String, ActualProperties> planNodeIdToActualPropertiesMap;
    HashMap<PlanNode, String> planNodeToLookUpStringMap;
    HashMap<PlanNode, String> stringRepMap;
    Multimap<String, String> locationToTableOrAliasNameMap;
    ArrayList<String> aliasList;
    ArrayList<String> aliasTableList;
    Multimap<String, String> duplicateLocationTableAliasNameMap;
    HashMap<PlanNode, JoinConstraintNode> planNodeToJoinConstraintMap;

    Metadata metadata;
    Session session;
    TypeProvider types;
    SqlParser parser;
    CostProvider costProvider;
    StatsProvider statsProvider;
    List<SubPlan> subPlans;
    Analysis analysis;

    public OptTrace(String dirPath, Metadata metadataParam, Session sessionParam, TypeProvider typesParam, SqlParser parserParam, Lookup lookUpParam, Memo memoParam,
            CostProvider costProviderParam,
            StatsProvider statsProviderParam)
    {
        requireNonNull(dirPath, "dirPath is null");

        indent = 0;
        incrIndent = 2;
        metadata = metadataParam;
        session = sessionParam;
        types = typesParam;
        parser = parserParam;
        lookUp = lookUpParam;
        memo = memoParam;
        uid = 0;
        uidStack = new Stack<Long>();
        queryInfo = null;
        outputQueryInfo = true;
        traceIdMap = new HashMap<String, Integer>();
        joinIdMap = new HashMap<String, Integer>();
        minusOne = Integer.valueOf(-1);
        joinStringMap = new HashMap<PlanNode, Pair<String, String>>();
        currentTraceId = 0;
        currentJoinId = 0;
        planConstraints = null;
        enumeratedJoins = new ArrayList<JoinNode>();
        prunedJoinIds = new HashMap<Integer, PruneReason>();
        validUnderConstraintsJoinIds = new ArrayList<Integer>();
        traceIdsAssigned = false;
        planNodeIdToPreferredPropertiesMap = new HashMap<String, PreferredProperties>();
        planNodeIdToActualPropertiesMap = new HashMap<String, ActualProperties>();
        planNodeToLookUpStringMap = new HashMap<PlanNode, String>();
        stringRepMap = new HashMap<PlanNode, String>();
        planNodeToJoinConstraintMap = new HashMap<PlanNode, JoinConstraintNode>();
        locationToTableOrAliasNameMap = HashMultimap.create();
        duplicateLocationTableAliasNameMap = HashMultimap.create();
        aliasList = new ArrayList<>();
        aliasTableList = new ArrayList<>();
        costProvider = costProviderParam;
        statsProvider = statsProviderParam;
        subPlans = new ArrayList<SubPlan>();
        analysis = null;

        Path path = Paths.get(dirPath);

        if (Files.exists(path)) {
            if (!dirPath.endsWith("/")) {
                dirPath = dirPath + "/";
            }

            String tryFileName = dirPath + "optTrace_0.txt";
            path = Paths.get(tryFileName);

            for (int i = 1; Files.exists(path); ++i) {
                tryFileName = dirPath + "optTrace_" + i + ".txt";
                path = Paths.get(tryFileName);
            }

            file = new File(tryFileName);

            try {
                fileWriter = new FileWriter(file, true);
                bufferedWriter = new BufferedWriter(fileWriter);
            }
            catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
        else {
            throw new PrestoException(GENERIC_INTERNAL_ERROR, format("Optimizer trace directory does not exist : %s", dirPath));
        }
    }

    public int getIndent()
    {
        return indent;
    }

    public Session session()
    {
        return session;
    }

    public void setTypeProvider(TypeProvider typesParam)
    {
        requireNonNull(typesParam, " type provider is null");
        types = typesParam;
    }

    public void addPlanNodeToPreferredPropertiesMapping(PlanNode planNode, PreferredProperties preferredProperties)
    {
        requireNonNull(planNode, "plan node is null");
        requireNonNull(preferredProperties, "preferred properties is null");
        planNodeIdToPreferredPropertiesMap.put(planNode.getId().getId(), preferredProperties);
    }

    public void addPrunedJoinId(Integer joinId, PruneReason reason)
    {
        requireNonNull(joinId, "join id is null");
        if (joinId == -1) {
            throw new PrestoException(GENERIC_INTERNAL_ERROR, "join id not set");
        }

        boolean add;
        if (reason == PruneReason.CONSTRAINT) {
            add = true;
        }
        else if (prunedJoinIds.get(joinId) == null) {
            add = true;
        }
        else {
            add = false;
        }

        if (add && prunedJoinIds.get(joinId) == null) {
            prunedJoinIds.put(joinId, reason);
        }
    }

    public PruneReason isPruned(Integer joinId)
    {
        requireNonNull(joinId, "join id is null");
        if (joinId == -1) {
            throw new PrestoException(GENERIC_INTERNAL_ERROR, "trace id not set");
        }

        return prunedJoinIds.get(joinId);
    }

    public boolean isValidUnderConstraints(Integer joinId)
    {
        requireNonNull(joinId, "join id is null");
        if (joinId == -1) {
            throw new PrestoException(GENERIC_INTERNAL_ERROR, "trace id not set");
        }

        return validUnderConstraintsJoinIds.contains(joinId);
    }

    public void setIsValidUnderConstraints(Integer joinId)
    {
        requireNonNull(joinId, "join id is null");
        if (joinId == -1) {
            throw new PrestoException(GENERIC_INTERNAL_ERROR, "trace id not set");
        }

        validUnderConstraintsJoinIds.add(joinId);
    }

    public void addEnumeratedJoin(PlanNode planNode)
    {
        requireNonNull(planNode, "join node is null");

        if (planNode instanceof JoinNode) {
            JoinNode joinNode = (JoinNode) planNode;
            if (!enumeratedJoins.contains(planNode)) {
                enumeratedJoins.add(joinNode);
            }
        }
        else if (planNode instanceof GroupReference) {
            GroupReference groupReference = (GroupReference) planNode;
            Stream<PlanNode> planNodes = lookUp.resolveGroup(groupReference);
            Optional<PlanNode> groupPlanNode = planNodes.findFirst();
            if (groupPlanNode.isPresent()) {
                PlanNode tmpNode = groupPlanNode.get();
                if (tmpNode instanceof JoinNode) {
                    if (!enumeratedJoins.contains(tmpNode)) {
                        enumeratedJoins.add((JoinNode) tmpNode);
                    }
                }
            }
        }
    }

    public BasicQueryInfo getQueryInfo()
    {
        return queryInfo;
    }

    public void setQueryInfo(BasicQueryInfo queryInfoParam)
    {
        queryInfo = queryInfoParam;
    }

    public void reinitialize(Lookup lookUpParam, Memo memoParam, CostProvider costProviderParam, StatsProvider statsProviderParam)
    {
        lookUp = lookUpParam;
        memo = memoParam;
        costProvider = costProviderParam;
        statsProvider = statsProviderParam;
    }

    public LinkedHashSet<TableScanNode> getTableScans(PlanNode planNode)
    {
        OptTraceContext optTraceContext = new OptTraceContext(this, VisitType.FIND_TABLES);
        planNode.accept(new OptTracePlanVisitor(), optTraceContext);

        return optTraceContext.tableScans;
    }

    public int getTableScanCnt(PlanNode planNode)
    {
        OptTraceContext optTraceContext = new OptTraceContext(this, VisitType.CNT_TABLES);
        planNode.accept(new OptTracePlanVisitor(), optTraceContext);

        return optTraceContext.tableCnt;
    }

    public Pair<String, String> getJoinStrings(PlanNode planNode)
    {
        Pair<String, String> joinStrings = this.joinStringMap.get(planNode);

        if (joinStrings == null) {
            OptTraceContext optTraceContext = new OptTraceContext(this, VisitType.BUILD_JOIN_STRING);
            planNode.accept(new OptTracePlanVisitor(), optTraceContext);
            String joinString = new String(optTraceContext.tableCnt + "-way " + optTraceContext.joinString);

            String joinConstraintString = joinConstraintString(planNode, false);

            joinStrings = new Pair<String, String>(joinString, joinConstraintString);
            joinStringMap.put(planNode, joinStrings);
        }

        return joinStrings;
    }

    public Lookup lookUp()
    {
        return lookUp;
    }

    public Memo memo()
    {
        return memo;
    }

    public StatsProvider statsProvider()
    {
        return statsProvider;
    }

    public CostProvider costProvider()
    {
        return costProvider;
    }

    public Long nextUid()
    {
        ++uid;
        return uid;
    }

    public void begin(String msgString, Object... args)
    {
        uidStack.push(Long.valueOf(uid + 1));
        if (msgString != null) {
            String beginString = new String("BEGIN : " + msgString);

            msg(beginString, true, args);
        }

        indent += incrIndent;
    }

    public void clearCaches()
    {
        locationToTableOrAliasNameMap.clear();
        duplicateLocationTableAliasNameMap.clear();
        aliasList.clear();
        aliasTableList.clear();
    }

    public Analysis analysis()
    {
        return this.analysis;
    }

    public void setAnalysis(Analysis analysis)
    {
        this.analysis = analysis;
    }

    public void checkForDuplicateTableName(String tableOrAliasName, String nodeLocation, boolean isAlias)
    {
        requireNonNull(tableOrAliasName, "table or alias name is null");
        requireNonNull(nodeLocation, "node location is null");

        if (isAlias) {
            aliasList.add(tableOrAliasName);
        }

        aliasTableList.add(tableOrAliasName);

        if (!duplicateLocationTableAliasNameMap.containsKey(nodeLocation)) {
            if (locationToTableOrAliasNameMap.containsEntry(nodeLocation, tableOrAliasName)) {
                locationToTableOrAliasNameMap.remove(nodeLocation, tableOrAliasName);
                duplicateLocationTableAliasNameMap.put(nodeLocation, tableOrAliasName);
            }
            else if (locationToTableOrAliasNameMap.containsKey(nodeLocation)) {
                List<String> tableAliasList = locationToTableOrAliasNameMap.get(nodeLocation).stream().collect(toList());

                checkArgument(tableAliasList.size() > 0);

                if (isAlias) {
                    locationToTableOrAliasNameMap.removeAll(nodeLocation);
                    locationToTableOrAliasNameMap.put(nodeLocation, tableOrAliasName);
                }
                else {
                    List<String> intersection = tableAliasList.stream()
                            .filter(aliasList::contains)
                            .distinct()
                            .collect(Collectors.toList());

                    if (intersection.size() == 0) {
                        locationToTableOrAliasNameMap.put(nodeLocation, tableOrAliasName);
                    }
                }
            }
            else {
                locationToTableOrAliasNameMap.put(nodeLocation, tableOrAliasName);
            }
        }

        return;
    }

    private void buildPlanConstraints(String queryString)
            throws IOException
    {
        planConstraints = null;
        int beginConstraintPos = queryString.indexOf("/*!");
        if (beginConstraintPos != -1) {
            planConstraints = new ArrayList<JoinConstraintNode>();
            int endConstraintPos = queryString.indexOf("*/", beginConstraintPos);
            String constraintString = queryString.substring(beginConstraintPos + 3, endConstraintPos);
            JoinConstraintNode.parse(constraintString, planConstraints);
        }
    }

    public void queryInfo()
    {
        if (outputQueryInfo) {
            this.msg("Query info :", true);
            this.incrIndent(1);
            if (queryInfo != null) {
                this.msg("Query string (id %s) :", true, queryInfo.getQueryId().getId());
                this.msg("  %s", true, queryInfo.getQuery());

                try {
                    buildPlanConstraints(queryInfo.getQuery());
                }
                catch (IOException e) {
                    throw new PrestoException(GENERIC_INTERNAL_ERROR, "Invalid join constraint");
                }
            }
            else {
                this.msg("<null>", true);
            }

            if (planConstraints != null) {
                this.msg("Constraints :", true);
                incrIndent(1);
                int cnt = 0;
                for (JoinConstraintNode joinConstraintNode : planConstraints) {
                    this.msg("%d : %s", true, cnt, joinConstraintNode.joinConstraintString());
                }
                decrIndent(1);
            }

            this.decrIndent(1);
            outputQueryInfo = false;
        }
    }

    public void end(String msgString, Object... args)
    {
        indent -= incrIndent;

        if (indent < 0) {
            throw new PrestoException(GENERIC_INTERNAL_ERROR, format("Optimizer trace indent < 0"));
        }

        if (uidStack.empty()) {
            throw new PrestoException(GENERIC_INTERNAL_ERROR, format("Optimizer trace UID stack empty"));
        }

        Long beginUid = uidStack.pop();

        if (msgString != null) {
            String endString = new String("END (for UID " + beginUid + ") : " + msgString);

            msg(endString, true, args);
        }
    }

    public void assignTraceIds(PlanNode planNode, Analysis analysis)
    {
        begin("assignTraceIds");

        if (!traceIdsAssigned) {
            if (analysis != null) {
                clearCaches();
                OptTraceTraversalVisitor statementVisitor = new OptTraceTraversalVisitor(this, analysis);
                statementVisitor.process(analysis.getStatement());
            }

            assignTableScanTraceIds(planNode);

            if (planConstraints != null) {
                for (JoinConstraintNode joinConstraintNode : planConstraints) {
                    joinConstraintNode.setJoinIdsFromTableOrAliasName(joinIdMap, locationToTableOrAliasNameMap);
                }
            }

            begin("location-to-table/alias map");

            for (String location : locationToTableOrAliasNameMap.keySet()) {
                List<String> nameAliasList = locationToTableOrAliasNameMap.get(location).stream().collect(toList());
                for (String nameOrAlias : nameAliasList) {
                    msg(location + " <=> " + nameOrAlias, true);
                }
            }

            end("location-to-table/alias map");

            traceIdsAssigned = true;
        }

        end("assignTraceIds");
    }

    private class TableScanComparator
            implements Comparator<TableScanNode>
    {
        public int compare(TableScanNode tableScan1, TableScanNode tableScan2)
        {
            String str1 = tableScan1.getTable().getConnectorHandle().toString();
            String str2 = tableScan2.getTable().getConnectorHandle().toString();

            int cmp = str1.compareTo(str2);

            return cmp;
        }
    }

    private class PlanNodeTableScanCntComparator
            implements Comparator<PlanNode>
    {
        private OptTrace optTrace;

        public PlanNodeTableScanCntComparator(OptTrace optTraceParam)
        {
            requireNonNull(optTraceParam, "opt trace is null");
            optTrace = optTraceParam;
        }

        public int compare(PlanNode planNode1, PlanNode planNode2)
        {
            int cnt1 = optTrace.getTableScanCnt(planNode1);
            int cnt2 = optTrace.getTableScanCnt(planNode2);

            int cmp;

            cmp = cnt1 - cnt2;

            if (cmp == 0) {
                Integer traceId1 = optTrace.getTraceId(planNode1);
                Integer traceId2 = optTrace.getTraceId(planNode2);

                cmp = traceId1.intValue() - traceId2.intValue();
            }

            return cmp;
        }
    }

    private class TableScanNameLocationComparator
            implements Comparator<TableScanNode>
    {
        private OptTrace optTrace;

        public TableScanNameLocationComparator(OptTrace optTraceParam)
        {
            requireNonNull(optTraceParam, "opt trace is null");
            optTrace = optTraceParam;
        }

        public int compare(TableScanNode tableScanNode1, TableScanNode tableScanNode2)
        {
            String name1 = tableName(tableScanNode1, optTrace);
            String name2 = tableName(tableScanNode2, optTrace);

            int cmp = name1.compareTo(name2);

            if (cmp == 0) {
                if (tableScanNode1.getSourceLocation().isPresent() && tableScanNode2.getSourceLocation().isPresent()) {
                    name1 = name1 + sourceLocationToString(tableScanNode1.getSourceLocation().get());
                    name2 = name2 + sourceLocationToString(tableScanNode2.getSourceLocation().get());

                    cmp = name1.compareTo(name2);
                }
            }

            return cmp;
        }
    }

    private String tableScanLookUpString(TableScanNode tableScanNode)
    {
        StringBuilder builder = new StringBuilder();
        String locationString;
        if (tableScanNode.getSourceLocation().isPresent()) {
            locationString = sourceLocationToString(tableScanNode.getSourceLocation().get());
            if (locationToTableOrAliasNameMap.containsKey(locationString)) {
                List<String> tableAliasNameList = locationToTableOrAliasNameMap.get(locationString).stream().collect(toList());
                checkArgument(tableAliasNameList.size() == 1, format("multiple (or zero) table name/aliases at location %s", locationString));
            }
            else {
                locationString = null;
            }
        }
        else {
            locationString = null;
        }

        if (locationString != null) {
            builder.append(locationString);
        }
        else {
            builder.append(tableScanNode.getId().getId());
        }

        return builder.toString();
    }

    @Immutable
    public static class Pair<K, V>
    {
        private final K key;
        private final V value;

        @JsonCreator
        public Pair(@JsonProperty("key") K key, @JsonProperty("value") V value)
        {
            this.key = requireNonNull(key, "key is null");
            this.value = requireNonNull(value, "value is null");
        }

        @JsonProperty
        public K getKey()
        {
            return key;
        }

        @JsonProperty
        public V getValue()
        {
            return value;
        }
    }

    private String getLookUpString(PlanNode planNode, boolean... ignoreDistributionType)
    {
        String lookUpString;
        boolean useCache;

        if (ignoreDistributionType.length == 0 || !ignoreDistributionType[0]) {
            lookUpString = planNodeToLookUpStringMap.get(planNode);
            useCache = true;
        }
        else {
            lookUpString = null;
            useCache = false;
        }

        if (lookUpString == null) {
            if (planNode instanceof TableScanNode) {
                lookUpString = tableScanLookUpString((TableScanNode) planNode);
            }
            else if (planNode instanceof GroupReference) {
                GroupReference groupReference = (GroupReference) planNode;
                Stream<PlanNode> planNodes = lookUp.resolveGroup(groupReference);
                Optional<PlanNode> groupPlanNode = planNodes.findFirst();
                if (groupPlanNode.isPresent()) {
                    PlanNode tmpNode = groupPlanNode.get();
                    lookUpString = getLookUpString(tmpNode);
                }
                else {
                    lookUpString = new String("Group Reference " + groupReference.getGroupId());
                }
            }
            else if (planNode instanceof JoinNode || planNode instanceof SemiJoinNode) {
                lookUpString = joinConstraintString(planNode, ignoreDistributionType);
            }
            else if (planNode instanceof ProjectNode || planNode instanceof ExchangeNode) {
                if (planNode.getSources() != null && planNode.getSources().size() == 1) {
                    lookUpString = getLookUpString(planNode.getSources().get(0), ignoreDistributionType);
                }
            }
            else if (planNode instanceof RemoteSourceNode) {
                RemoteSourceNode remoteSourceNode = (RemoteSourceNode) planNode;
                lookUpString = new String("RemoteSource");

                for (PlanFragmentId planFragmentId : remoteSourceNode.getSourceFragmentIds()) {
                    lookUpString = lookUpString + " (" + planFragmentId.getId() + ")";
                }
            }
            else if (planNode instanceof ValuesNode) {
                ValuesNode valuesNode = (ValuesNode) planNode;
                lookUpString = new String("Values ") + planNode.getId().getId() + " (";

                boolean first = true;
                for (VariableReferenceExpression outExpr : valuesNode.getOutputVariables()) {
                    if (!first) {
                        lookUpString = lookUpString + " ";
                    }

                    lookUpString = lookUpString + outExpr.getName();
                    first = false;
                }

                lookUpString = lookUpString + ")";
            }

            if (lookUpString == null) {
                String className = planNode.getClass().getSimpleName().toUpperCase();
                if (className.substring(className.length() - 4).equals("NODE")) {
                    className = className.substring(0, className.length() - 4);
                }

                StringBuilder builder = new StringBuilder(className);

                if (planNode.getSources().size() > 1) {
                    builder.append("(");
                }

                int cnt = 0;
                for (PlanNode source : planNode.getSources()) {
                    if (cnt > 0) {
                        builder.append(" ");
                    }

                    builder.append("(");
                    builder.append(getLookUpString(source, ignoreDistributionType));

                    builder.append(")");
                    ++cnt;
                }

                if (planNode.getSources().size() > 1) {
                    builder.append(")");
                }

                lookUpString = builder.toString();
            }
        }

        if (useCache) {
            planNodeToLookUpStringMap.put(planNode, lookUpString);
        }

        return lookUpString;
    }

    public void assignTableScanTraceIds(PlanNode node)
    {
        begin("assignTableScanTraceIds");
        LinkedHashSet<TableScanNode> tableScans = getTableScans(node);

        if (tableScans != null) {
            TableScanNameLocationComparator compare = new TableScanNameLocationComparator(this);

            ArrayList<TableScanNode> tableScansArray = new ArrayList<>(tableScans);
            tableScansArray.sort(compare);

            begin("location-to-id map");

            StringBuilder builder = new StringBuilder();
            for (TableScanNode tableScanNode : tableScansArray) {
                String lookUpString = tableScanLookUpString(tableScanNode);
                int traceId = newTraceId(lookUpString);
                newJoinId(lookUpString);

                builder.append(lookUpString);
                builder.append(" => ");
                builder.append(traceId);

                msg(builder.toString(), true);

                builder.setLength(0);
            }

            end("location-to-id map");
        }

        end("assignTableScanTraceIds");
    }

    public Pair<ArrayList<Integer>, ArrayList<Integer>> traceIds(JoinNode joinNode)
    {
        return null;
    }

    private Integer newTraceId(String lookUpString)
    {
        requireNonNull(lookUpString, "lookup string is null");

        Integer traceId = traceIdMap.get(lookUpString);

        if (traceId == null) {
            traceId = Integer.valueOf(currentTraceId);
            traceIdMap.put(lookUpString, traceId);
            traceIdMap.put(traceId.toString(), traceId);
            ++currentTraceId;
        }

        return traceId;
    }

    private Integer newJoinId(String lookUpString)
    {
        requireNonNull(lookUpString, "lookup string is null");

        Integer joinId = joinIdMap.get(lookUpString);

        if (joinId == null) {
            joinId = Integer.valueOf(currentJoinId);
            joinIdMap.put(lookUpString, joinId);
            ++currentJoinId;
        }

        return joinId;
    }

    public Integer getTraceId(PlanNode planNode)
    {
        Integer traceId = minusOne;
        String lookUpString;

        lookUpString = getLookUpString(planNode);

        traceId = traceIdMap.get(lookUpString);

        if (traceId == null) {
            traceId = Integer.valueOf(currentTraceId);
            traceIdMap.put(lookUpString, traceId);
            ++currentTraceId;
        }

        return traceId;
    }

    public Integer getJoinId(PlanNode planNode, boolean... ignoreDistributionType)
    {
        Integer joinId = minusOne;

        String lookUpString;

        lookUpString = getLookUpString(planNode, ignoreDistributionType);

        requireNonNull(lookUpString, "lookup string is null");

        joinId = joinIdMap.get(lookUpString);

        if (joinId == null) {
            joinId = Integer.valueOf(currentJoinId);
            joinIdMap.put(lookUpString, joinId);
            ++currentJoinId;
        }

        return joinId;
    }

    Integer getJoinId(String lookUpString)
    {
        Integer joinId = joinIdMap.get(lookUpString);
        return joinId;
    }

    public static void begin(Optional<OptTrace> optTraceParam, String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.begin(msgString, args));
    }

    public static void clearCaches(Optional<OptTrace> optTraceParam)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.clearCaches());
    }

    public static void setAnalysis(Optional<OptTrace> optTraceParam, Analysis analysis)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.setAnalysis(analysis));
    }

    public static void checkForDuplicateTableName(Optional<OptTrace> optTraceParam, String tableOrAliasName, String nodeLocation, boolean isAlias)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.checkForDuplicateTableName(tableOrAliasName, nodeLocation, isAlias));
    }

    public static void addPrunedJoinId(Optional<OptTrace> optTraceParam, Integer joinId, PruneReason reason)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.addPrunedJoinId(joinId, reason));
    }

    public static void addPlanNodeToPreferredPropertiesMapping(Optional<OptTrace> optTraceParam, PlanNode planNode, PreferredProperties preferredProperties)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.addPlanNodeToPreferredPropertiesMapping(planNode, preferredProperties));
    }

    public static void tracePlanNodeStatsEstimate(Optional<OptTrace> optTraceParam, PlanNode planNode, int indentCnt, String msgString, Object... args)
    {
        if (optTraceParam.isPresent()) {
            optTraceParam.get().tracePlanNodeStatsEstimate(planNode, indentCnt, msgString, args);
        }
    }

    public static void traceMemo(Optional<OptTrace> optTraceParam)
    {
        if (optTraceParam.isPresent()) {
            optTraceParam.get().traceMemo();
        }
    }

    public void tracePlanNodeStatsEstimate(PlanNode planNode, int indentCnt, String msgString, Object... args)
    {
        incrIndent(indentCnt);
        if (statsProvider != null) {
            try {
                PlanNodeStatsEstimate stats = statsProvider.getStats(planNode);
                if (stats != null) {
                    tracePlanNodeStatsEstimate(stats, 0, msgString);
                }
            }
            catch (RuntimeException e) {
                msg("Stats lookup failed.", true);
            }
        }
        else {
            msg("No stats provider.", true);
        }

        decrIndent(indentCnt);
    }

    public static void traceVariableReferenceExpressionList(Optional<OptTrace> optTraceParam, List<VariableReferenceExpression> varList, int indentCnt,
            String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.traceVariableReferenceExpressionList(varList, indentCnt, msgString, args));
    }

    public static void tracePreferredProperties(Optional<OptTrace> optTraceParam, PreferredProperties preferredProperties, PlanNode planNode, int indentCnt,
            String msgString, Object... args)
    {
        if (preferredProperties != null) {
            optTraceParam.ifPresent(optTrace -> optTrace.tracePreferredProperties(preferredProperties, indentCnt, msgString, args));
        }
    }

    public static PruneReason isPruned(Optional<OptTrace> optTraceParam, Integer traceId)
    {
        PruneReason pruned;
        if (optTraceParam.isPresent()) {
            OptTrace optTrace = optTraceParam.get();
            pruned = optTrace.isPruned(traceId);
        }
        else {
            pruned = null;
        }

        return pruned;
    }

    public static void queryInfo(Optional<OptTrace> optTraceParam)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.queryInfo());
    }

    public static void addEnumeratedJoin(Optional<OptTrace> optTraceParam, PlanNode planNode)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.addEnumeratedJoin(planNode));
    }

    public static void traceJoinIdMap(Optional<OptTrace> optTraceParam, int indentCnt, String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.traceJoinIdMap(indentCnt, msgString, args));
    }

    public static void trace(Optional<OptTrace> optTraceParam, PlanNode planNode, int indentCnt, String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.tracePlanNode(planNode, indentCnt, msgString, args));
    }

    public static void trace(Optional<OptTrace> optTraceParam, PlanNode planNode, int indentCnt, String msgString, int maxDepth, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.tracePlanNode(planNode, indentCnt, msgString, maxDepth, args));
    }

    public static void traceEnumeratedJoins(Optional<OptTrace> optTraceParam, PlanNode root, CostProvider costProvider, StatsProvider statsProvider,
            int indentCnt, String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.traceEnumeratedJoins(root, costProvider, statsProvider, indentCnt, msgString, args));
    }

    public static void traceJoinConstraint(Optional<OptTrace> optTraceParam, PlanNode planNode, int indentCnt, String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.traceJoinConstraint(planNode, indentCnt, msgString, args));
    }

    public static void trace(Optional<OptTrace> optTraceParam, PlanCostEstimate planCostEstimate, int indentCnt, String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.tracePlanCostEstimate(planCostEstimate, indentCnt, msgString, args));
    }

    public static void msg(Optional<OptTrace> optTraceParam, String msgString, boolean eol, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.msg(msgString, eol, args));
    }

    public static void end(Optional<OptTrace> optTraceParam, String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.end(msgString, args));
    }

    public static void incrIndent(Optional<OptTrace> optTraceParam, int indentCnt)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.incrIndent(indentCnt));
    }

    public static void decrIndent(Optional<OptTrace> optTraceParam, int indentCnt)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.decrIndent(indentCnt));
    }

    public static void trace(Optional<OptTrace> optTraceParam, Set<Integer> partition, String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.tracePartition(partition, msgString, args));
    }

    public static void trace(Optional<OptTrace> optTraceParam, Set<PlanNode> sources, int indentCnt, String msgString, Object... args)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.traceJoinSources(sources, indentCnt, msgString, args));
    }

    private static PlanNode findRootJoin(PlanNode planNode, Lookup lookUp)
    {
        requireNonNull(planNode, "plan node is null");

        PlanNode rootJoinNode = null;
        if (planNode instanceof JoinNode || planNode instanceof SemiJoinNode) {
            rootJoinNode = planNode;
        }
        else if (planNode instanceof GroupReference) {
            GroupReference groupReference = (GroupReference) planNode;
            Stream<PlanNode> planNodes = lookUp.resolveGroup(groupReference);
            Optional<PlanNode> groupPlanNode = planNodes.findFirst();
            if (groupPlanNode.isPresent()) {
                PlanNode tmpNode = groupPlanNode.get();
                rootJoinNode = findRootJoin(tmpNode, lookUp);
            }
        }
        else {
            for (PlanNode source : planNode.getSources()) {
                PlanNode sourceRootJoinNode = findRootJoin(source, lookUp);
                if (sourceRootJoinNode != null) {
                    if (rootJoinNode != null) {
                        rootJoinNode = null;
                        break;
                    }
                    else {
                        rootJoinNode = sourceRootJoinNode;
                    }
                }
            }
        }

        return rootJoinNode;
    }

    public String joinConstraintString(PlanNode planNode, boolean... ignoreDistributionType)
    {
        JoinConstraintNode joinConstraintNode = joinConstraintNode(planNode, null, ignoreDistributionType);
        String joinConstraintString;
        if (joinConstraintNode != null) {
            joinConstraintString = joinConstraintNode.joinConstraintString();
        }
        else {
            joinConstraintString = null;
        }

        return joinConstraintString;
    }

    private JoinConstraintNode joinConstraintNode(PlanNode planNode, PlanNode rootJoinNode, boolean... ignoreDistributionType)
    {
        JoinConstraintNode joinConstraintNode = null;
        boolean useCache;

        if (ignoreDistributionType.length == 0 || !ignoreDistributionType[0]) {
            joinConstraintNode = planNodeToJoinConstraintMap.get(planNode);
            useCache = true;
        }
        else {
            useCache = false;
        }

        if (joinConstraintNode == null) {
            if (planNode instanceof GroupReference) {
                GroupReference groupReference = (GroupReference) planNode;
                Stream<PlanNode> planNodes = lookUp.resolveGroup(groupReference);
                Optional<PlanNode> groupPlanNode = planNodes.findFirst();
                if (groupPlanNode.isPresent()) {
                    PlanNode tmpNode = groupPlanNode.get();
                    joinConstraintNode = joinConstraintNode(tmpNode, rootJoinNode, ignoreDistributionType);
                }
                else {
                    joinConstraintNode = new JoinConstraintNode(Long.valueOf(getJoinId(groupReference)), groupReference, JoinConstraintNode.ConstraintType.JOIN);
                }
            }
            else {
                if (planNode instanceof TableScanNode) {
                    TableScanNode tableScanNode = (TableScanNode) planNode;
                    Integer joinId = getJoinId(planNode);

                    String tableOrAliasName = null;

                    if (tableScanNode.getSourceLocation().isPresent()) {
                        String locationString = sourceLocationToString(tableScanNode.getSourceLocation().get());

                        if (locationToTableOrAliasNameMap.containsKey(locationString)) {
                            List<String> tableAliasNameList = locationToTableOrAliasNameMap.get(locationString).stream().collect(toList());
                            checkArgument(tableAliasNameList.size() == 1, format("multiple (or zero) table name/aliases at location %s", locationString));

                            tableOrAliasName = tableAliasNameList.get(0);

                            final String checkName = tableOrAliasName;
                            long count = locationToTableOrAliasNameMap.values().stream().filter(name -> checkName.equals(name)).count();

                            if (count > 1) {
                                tableOrAliasName = null;
                            }
                        }
                    }

                    joinConstraintNode = new JoinConstraintNode(tableScanNode, Long.valueOf(joinId), tableOrAliasName, JoinConstraintNode.ConstraintType.JOIN);
                }
                else if (planNode instanceof JoinNode) {
                    JoinNode joinNode = (JoinNode) planNode;
                    joinConstraintNode = new JoinConstraintNode(joinNode, ignoreDistributionType);

                    if (rootJoinNode == null) {
                        rootJoinNode = joinNode;
                    }

                    JoinConstraintNode leftJoinConstraintNode = joinConstraintNode(joinNode.getLeft(), rootJoinNode, ignoreDistributionType);
                    joinConstraintNode.appendChild(leftJoinConstraintNode);
                    JoinConstraintNode rightJoinConstraintNode = joinConstraintNode(joinNode.getRight(), rootJoinNode, ignoreDistributionType);
                    joinConstraintNode.appendChild(rightJoinConstraintNode);

                    String joinConstraintString = joinConstraintNode.joinConstraintString();
                    Integer joinId = joinIdMap.get(joinConstraintString);

                    if (joinId == null) {
                        joinId = newJoinId(joinConstraintString);
                    }

                    joinConstraintNode.setId(Long.valueOf(joinId));
                }
                else if (planNode instanceof SemiJoinNode) {
                    SemiJoinNode semiJoinNode = (SemiJoinNode) planNode;
                    joinConstraintNode = new JoinConstraintNode(semiJoinNode, ignoreDistributionType);

                    if (rootJoinNode == null) {
                        rootJoinNode = semiJoinNode;
                    }

                    JoinConstraintNode probeJoinConstraintNode = joinConstraintNode(semiJoinNode.getProbe(), rootJoinNode, ignoreDistributionType);
                    joinConstraintNode.appendChild(probeJoinConstraintNode);
                    JoinConstraintNode buildJoinConstraintNode = joinConstraintNode(semiJoinNode.getBuild(), rootJoinNode, ignoreDistributionType);
                    joinConstraintNode.appendChild(buildJoinConstraintNode);
                    String joinConstraintString = joinConstraintNode.joinConstraintString();
                    Integer joinId = joinIdMap.get(joinConstraintString);

                    if (joinId == null) {
                        joinId = newJoinId(joinConstraintString);
                    }

                    joinConstraintNode.setId(Long.valueOf(joinId));
                }
                else if (planNode instanceof ProjectNode || planNode instanceof ExchangeNode) {
                    if (planNode.getSources() != null && planNode.getSources().size() == 1) {
                        joinConstraintNode = joinConstraintNode(planNode.getSources().get(0), rootJoinNode, ignoreDistributionType);
                    }
                }
                else if (planNode instanceof RemoteSourceNode) {
                    RemoteSourceNode remoteSourceNode = (RemoteSourceNode) planNode;
                    List<PlanFragmentId> fragmentIds = remoteSourceNode.getSourceFragmentIds();

                    if (fragmentIds.size() == 1) {
                        PlanFragmentId planFragmentId = fragmentIds.get(0);
                        SubPlan subPlan = findSubPlan(planFragmentId);

                        if (subPlan != null) {
                            PlanNode fragmentRootNode = subPlan.getFragment().getRoot();

                            joinConstraintNode = joinConstraintNode(fragmentRootNode, rootJoinNode, ignoreDistributionType);
                        }
                    }
                }

                if (joinConstraintNode == null) {
                    if (rootJoinNode == null) {
                        if (planNode instanceof JoinNode || planNode instanceof SemiJoinNode) {
                            rootJoinNode = findRootJoin(planNode, lookUp);
                        }

                        if (rootJoinNode != null) {
                            joinConstraintNode = joinConstraintNode(rootJoinNode, null, ignoreDistributionType);
                        }
                        else {
                            joinConstraintNode = new JoinConstraintNode(Long.valueOf(getJoinId(planNode, ignoreDistributionType)), planNode,
                                    JoinConstraintNode.ConstraintType.JOIN);
                        }
                    }
                    else {
                        joinConstraintNode = new JoinConstraintNode(Long.valueOf(getJoinId(planNode)), planNode, JoinConstraintNode.ConstraintType.JOIN);
                    }
                }
            }

            if (useCache) {
                planNodeToJoinConstraintMap.put(planNode, joinConstraintNode);
            }
        }

        return joinConstraintNode;
    }

    public static JoinConstraintNode joinConstraintNode(Optional<OptTrace> optTraceParam, JoinNode joinNode, boolean ignoreDistributionType)
    {
        JoinConstraintNode joinConstraintNode = null;
        if (optTraceParam.isPresent()) {
            joinConstraintNode = optTraceParam.get().joinConstraintNode(joinNode, null, ignoreDistributionType);
        }

        return joinConstraintNode;
    }

    public void addSubPlans(List<SubPlan> subPlansParam)
    {
        requireNonNull(subPlansParam);
        subPlans.addAll(subPlansParam);
    }

    public SubPlan findSubPlan(PlanFragmentId planFragmentId)
    {
        SubPlan subPlan = null;
        for (SubPlan currentSubPlan : subPlans) {
            if (currentSubPlan.getFragment().getId() == planFragmentId) {
                subPlan = currentSubPlan;
                break;
            }
        }

        return subPlan;
    }

    public static void addSubPlans(Optional<OptTrace> optTraceParam, List<SubPlan> subPlansParam)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.addSubPlans(subPlansParam));
    }

    public static JoinConstraintNode joinConstraintNode(Optional<OptTrace> optTraceParam, SemiJoinNode semiJoinNode, boolean ignoreDistributionType)
    {
        JoinConstraintNode joinConstraintNode = null;
        if (optTraceParam.isPresent()) {
            joinConstraintNode = optTraceParam.get().joinConstraintNode(semiJoinNode, null, ignoreDistributionType);
        }

        return joinConstraintNode;
    }

    public static void assignTraceIds(Optional<OptTrace> optTraceParam, PlanNode node, Analysis analysis)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.assignTraceIds(node, analysis));
    }

    private void addJoinConstraintNode(PlanNode node)
    {
        JoinConstraintNode joinConstraintNode = joinConstraintNode(node, null);
        planConstraints.add(joinConstraintNode);
    }

    public static void addJoinConstraintNode(Optional<OptTrace> optTraceParam, PlanNode node)
    {
        optTraceParam.ifPresent(optTrace -> optTrace.addJoinConstraintNode(node));
    }

    public boolean satisfiesAnyJoinConstraint(PlanNode planNode, boolean... ignoreDistributionType)
    {
        requireNonNull(planNode, "plan node is null");
        boolean satifiesAny = false;

        if (planConstraints != null && planConstraints.size() > 0 &&
                (planNode instanceof JoinNode || planNode instanceof SemiJoinNode || planNode instanceof GroupReference
                        || planNode instanceof TableScanNode)) {
            JoinConstraintNode joinConstraintNode = joinConstraintNode(planNode, null, ignoreDistributionType);
            requireNonNull(joinConstraintNode, "join constraint is null");

            satifiesAny = joinConstraintNode.satisfiesAnyConstraint(planConstraints, ignoreDistributionType);
        }

        return satifiesAny;
    }

    public Long getCardinality(PlanNode planNode)
    {
        requireNonNull(planNode, "plan node is null");
        Long cardinality = null;

        if (planConstraints != null && planConstraints.size() > 0) {
            JoinConstraintNode joinConstraintNode = joinConstraintNode(planNode, null, true);
            requireNonNull(joinConstraintNode, "join constraint is null");

            cardinality = joinConstraintNode.cardinality(planConstraints, this);
        }

        return cardinality;
    }

    public static boolean constraintsPresent(Optional<OptTrace> optTraceParam)
    {
        boolean constraintsPresent = false;
        if (optTraceParam.isPresent()) {
            constraintsPresent = (optTraceParam.get().planConstraints != null && optTraceParam.get().planConstraints.size() > 0);
        }

        return constraintsPresent;
    }

    public static boolean joinConstraintsPresent(Optional<OptTrace> optTraceParam)
    {
        boolean joinConstraintsPresent = false;
        if (optTraceParam.isPresent()) {
            if (optTraceParam.get().planConstraints != null && optTraceParam.get().planConstraints.size() > 0) {
                for (JoinConstraintNode constraint : optTraceParam.get().planConstraints) {
                    if (constraint.constraintType() != null && constraint.constraintType() == JoinConstraintNode.ConstraintType.JOIN) {
                        joinConstraintsPresent = true;
                        break;
                    }
                }
            }
        }

        return joinConstraintsPresent;
    }

    public static boolean satisfiesAnyJoinConstraint(Optional<OptTrace> optTraceParam, PlanNode planNode, boolean... ignoreDistributionType)
    {
        boolean satifiesAny = false;
        if (optTraceParam.isPresent()) {
            satifiesAny = optTraceParam.get().satisfiesAnyJoinConstraint(planNode, ignoreDistributionType);
        }

        return satifiesAny;
    }

    public static PlanNodeStatsEstimate stats(Optional<OptTrace> optTraceParam, PlanNode planNode, PlanNodeStatsEstimate stats)
    {
        PlanNodeStatsEstimate newStats = null;

        if (optTraceParam.isPresent()) {
            newStats = optTraceParam.get().planNodeStats(planNode, stats);
        }

        return newStats;
    }

    public PlanNodeStatsEstimate planNodeStats(PlanNode planNode, PlanNodeStatsEstimate stats)
    {
        PlanNodeStatsEstimate newStats = null;

        if (stats != null) {
            Long cardinality = getCardinality(planNode);

            if (cardinality != null) {
                double cardinalityAsDouble = cardinality.doubleValue();
                double factor = cardinalityAsDouble / stats.getOutputRowCount();
                double totalSize = round(factor * stats.getOutputSizeInBytes(), 0);
                PlanNodeStatsEstimate.Builder builder = PlanNodeStatsEstimate.buildFrom(stats);
                builder.setOutputRowCount(cardinality.doubleValue());
                builder.setTotalSize(totalSize);
                builder.setConfident(true);
                newStats = builder.build();
            }
        }

        return newStats;
    }

    public static boolean valid(Optional<OptTrace> optTraceParam, PlanNode planNode)
    {
        boolean valid;

        if (optTraceParam.isPresent()) {
            OptTrace optTrace = optTraceParam.get();

            Integer joinId = optTrace.getJoinId(planNode);

            PruneReason reason = optTrace.isPruned(joinId);
            if (reason != null) {
                valid = false;
            }
            else if (optTrace.isValidUnderConstraints(joinId)) {
                valid = true;
            }
            else if (optTrace.planConstraints != null && optTrace.planConstraints.size() > 0) {
                JoinConstraintNode joinConstraintNode = optTrace.joinConstraintNode(planNode, null, false);
                valid = joinConstraintNode.joinIsValid(optTrace.planConstraints, optTrace);

                if (valid) {
                    optTrace.setIsValidUnderConstraints(joinId);
                }
                else {
                    reason = PruneReason.CONSTRAINT;
                    optTrace.addPrunedJoinId(joinId, reason);
                }
            }
            else {
                valid = true;
            }

            if (reason != null) {
                Pair<String, String> joinStrings = optTrace.getJoinStrings(planNode);
                requireNonNull(joinStrings, "join strings are null");
                requireNonNull(joinStrings.getKey(), "join string is null");
                optTrace.msg("Join not valid (** PRUNED BY %s **) : (%s , join id %d)",
                        true, reason.getString().toUpperCase(), joinStrings.getKey(), joinId.intValue());
            }
        }
        else {
            valid = true;
        }

        return valid;
    }

    public enum VisitType
    {
        NONE, PRINT, FIND_TABLES, BUILD_JOIN_STRING, CNT_TABLES, CNT_JOINS
    }

    public enum PruneReason
    {
        COST("cost"),
        CONSTRAINT("constraint");

        private String string;

        PruneReason(String stringRep)
        {
            this.string = stringRep;
        }

        public String getString()
        {
            return string;
        }
    }

    private class OptTraceContext
    {
        private OptTrace optTrace;
        LinkedHashSet<TableScanNode> tableScans;
        VisitType visitType;
        String joinString;
        int tableCnt;
        int joinCnt;

        public OptTraceContext(OptTrace optTraceParam, VisitType visitTypeParam)
        {
            requireNonNull(optTraceParam, "trace is null");
            optTrace = optTraceParam;
            visitType = visitTypeParam;
            joinString = null;
            tableCnt = 0;
            joinCnt = 0;
        }

        public void clearTableScans()
        {
            if (tableScans != null) {
                tableScans.clear();
            }
        }

        public void clearVisitType()
        {
            visitType = null;
        }

        public void clear()
        {
            clearVisitType();
            clearTableScans();
            joinString = null;
            tableCnt = 0;
        }

        public OptTrace optTrace()
        {
            return optTrace;
        }

        public void addTableScan(TableScanNode tableScanNode)
        {
            if (tableScans == null) {
                tableScans = new LinkedHashSet<TableScanNode>();
            }

            tableScans.add(tableScanNode);
        }

        LinkedHashSet<TableScanNode> tableScans()
        {
            return tableScans;
        }
    }

    public String tableScansToString(LinkedHashSet<TableScanNode> tableScans)
    {
        requireNonNull(tableScans, "tableScans is null");
        List<String> nameList = new ArrayList<String>();
        for (TableScanNode tableScan : tableScans) {
            String name = tableName(tableScan, this);
            nameList.add(name);
        }

        Collections.sort(nameList);

        StringBuilder builder = new StringBuilder("(");

        if (nameList.size() > 1) {
            builder = new StringBuilder("Join(");
        }
        else {
            builder = new StringBuilder("(");
        }

        boolean first = true;
        for (String name : nameList) {
            if (!first) {
                builder.append(" ");
            }

            builder.append(name);

            first = false;
        }

        builder.append(")");

        return builder.toString();
    }

    public static String nodeLocation(Node node)
    {
        String locationString;
        if (node.getLocation().isPresent()) {
            locationString = nodeLocationToString(node.getLocation().get());
        }
        else {
            locationString = null;
        }

        return locationString;
    }

    public static String nodeLocationToString(NodeLocation location)
    {
        String locationString = new String(location.getLineNumber() + ":" + location.getColumnNumber());

        return locationString;
    }

    public static String sourceLocationToString(SourceLocation location)
    {
        String locationString = new String(location.getLine() + ":" + location.getColumn());

        return locationString;
    }

    private static class OptTraceTraversalVisitor
            extends DefaultTraversalVisitor<RelationPlan, SqlPlannerContext>
    {
        private final OptTrace optTrace;
        private final Analysis analysis;

        OptTraceTraversalVisitor(OptTrace optTraceParam, Analysis analysisParam)
        {
            requireNonNull(optTraceParam, "null opt trace");
            requireNonNull(analysisParam, "null analysis");
            optTrace = optTraceParam;
            analysis = analysisParam;
        }

        @Override
        public RelationPlan process(Node node, @Nullable SqlPlannerContext context)
        {
            return super.process(node, context);
        }

        @Override
        protected RelationPlan visitQuery(Query node, SqlPlannerContext context)
        {
            //node.getWith().ifPresent(with -> process(with, context));

            process(node.getQueryBody(), context);

            node.getOrderBy().ifPresent(orderBy -> process(orderBy, context));

            return null;
        }

        @Override
        protected RelationPlan visitAliasedRelation(AliasedRelation node, SqlPlannerContext context)
        {
            requireNonNull(node.getAlias(), "alias is null");

            String aliasName = node.getAlias().getValue();
            String locationString;
            if (node.getLocation().isPresent()) {
                locationString = nodeLocationToString(node.getLocation().get());
            }
            else {
                return null;
            }

            optTrace.checkForDuplicateTableName(aliasName, locationString, true);

            Relation relation = node.getRelation();

            if (relation instanceof Table) {
                Table table = (Table) relation;
                if (table.getName().toString().equals(aliasName)) {
                    return null;
                }
            }

            return process(relation, context);
        }

        @Override
        protected RelationPlan visitTable(Table node, SqlPlannerContext context)
        {
            Query namedQuery = analysis.getNamedQuery(node);

            if (namedQuery != null) {
                return process(namedQuery, context);
            }

            String locationString;
            if (node.getLocation().isPresent()) {
                locationString = optTrace.nodeLocationToString(node.getLocation().get());
            }
            else {
                return null;
            }

            optTrace.checkForDuplicateTableName(node.getName().toString(), locationString, false);

            return null;
        }
    }

    private static class OptTracePlanVisitor
            extends InternalPlanVisitor<PlanNode, OptTraceContext>
    {
        private int currentDepth;
        private int maxDepth;
        public OptTracePlanVisitor()
        {
            currentDepth = 0;
            maxDepth = 10000;
        }

        public OptTracePlanVisitor(int maxDepthParam)
        {
            currentDepth = 0;
            maxDepth = maxDepthParam;
        }

        private void incrementDepth()
        {
            ++currentDepth;
        }

        private void decrementDepth()
        {
            --currentDepth;
        }

        private boolean checkDepth()
        {
            boolean check;
            if (maxDepth >= 0 && currentDepth > maxDepth) {
                check = false;
            }
            else {
                check = true;
            }

            return check;
        }

        @Override
        public PlanNode visitPlan(PlanNode planNode, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();

            switch (optTraceContext.visitType) {
                case PRINT: {
                    Integer joinId = optTrace.getJoinId(planNode);
                    optTrace.msg(planNode.getClass().getSimpleName() + " " + "(node id " + planNode.getId()
                            + ", join id " + joinId + ")", true);

                    optTrace.traceVariableReferenceExpressionList(planNode.getOutputVariables(), 1, "Output variables :");
                    optTrace.tracePreferredPropertiesForPlanNode(planNode, 1, "Preferred properties :");
                    optTrace.tracePlanNodeStatsEstimate(planNode, 1, "Estimated stats :");

                    int childId = 0;
                    for (PlanNode child : planNode.getSources()) {
                        if (checkDepth()) {
                            optTrace.incrIndent(1);
                            optTrace.msg("Child %d :", true, childId);
                            optTrace.incrIndent(1);
                            incrementDepth();
                            child.accept(this, optTraceContext);
                            optTrace.decrIndent(2);
                            decrementDepth();
                        }
                        else {
                            optTrace.incrIndent(1);
                            optTrace.msg("Child %d : ...", true, childId);
                            optTrace.decrIndent(1);
                        }

                        ++childId;
                    }

                    break;
                }

                case BUILD_JOIN_STRING: {
                    if (planNode.getSources().size() > 1) {
                        int childId = 0;
                        for (PlanNode child : planNode.getSources()) {
                            if (optTraceContext.joinString == null) {
                                optTraceContext.joinString = new String();
                            }

                            if (childId == 0) {
                                optTraceContext.joinString = optTraceContext.joinString + "(";
                            }
                            else {
                                optTraceContext.joinString = optTraceContext.joinString + " ";
                            }

                            incrementDepth();
                            child.accept(this, optTraceContext);
                            decrementDepth();
                            ++childId;
                        }

                        if (childId > 0) {
                            optTraceContext.joinString = optTraceContext.joinString + ")";
                        }
                    }
                    else if (planNode.getSources().size() == 0) {
                        Integer traceId = optTrace.getTraceId(planNode);
                        if (optTraceContext.joinString == null) {
                            optTraceContext.joinString = new String();
                        }

                        optTraceContext.joinString = optTraceContext.joinString + format("%s-%s", planNode.getClass().getSimpleName(), traceId);
                    }
                    else {
                        for (PlanNode child : planNode.getSources()) {
                            incrementDepth();
                            child.accept(this, optTraceContext);
                            decrementDepth();
                        }
                    }

                    break;
                }

                default: {
                    for (PlanNode child : planNode.getSources()) {
                        incrementDepth();
                        child.accept(this, optTraceContext);
                        decrementDepth();
                    }
                }
            }

            return null;
        }

        @Override
        public PlanNode visitApply(ApplyNode applyNode, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();

            switch (optTraceContext.visitType) {
                case PRINT: {
                    Integer joinId = optTrace.getJoinId(applyNode);
                    optTrace.msg(applyNode.getClass().getSimpleName() + " " + "(node id " + applyNode.getId()
                            + ", join id " + joinId + ")", true);

                    optTrace.incrIndent(1);
                    optTrace.msg("May participate in anti-join? : %s", true, applyNode.getMayParticipateInAntiJoin() ? "true" : "false");

                    Assignments subqueryAssignments = applyNode.getSubqueryAssignments();
                    Map<VariableReferenceExpression, RowExpression> assignmentMap = subqueryAssignments.getMap();
                    optTrace.msg("Subquery assignments :", true);
                    optTrace.incrIndent(1);
                    int cnt = 0;
                    for (Map.Entry<VariableReferenceExpression, RowExpression> assignmentMapEntry : assignmentMap.entrySet()) {
                        optTrace.msg("%d : %s => %s", true, cnt, assignmentMapEntry.getKey().getName(),
                                assignmentMapEntry.getValue().toString());
                        ++cnt;
                    }
                    optTrace.decrIndent(1);

                    String expressionString = Joiner.on(" AND ").join(subqueryAssignments.getExpressions());
                    optTrace.msg("Expression string : %s", true, expressionString);

                    optTrace.traceVariableReferenceExpressionList(subqueryAssignments.getVariables().stream().collect(toList()), 0, "Assignment output variables :");

                    cnt = 0;
                    for (RowExpression expression : subqueryAssignments.getExpressions()) {
                        if (expression instanceof InSubqueryExpression) {
                            if (cnt == 0) {
                                optTrace.msg("In subquery expression vars :", true);
                            }

                            InSubqueryExpression inPredicate = (InSubqueryExpression) expression;

                            VariableReferenceExpression leftVariableReference = inPredicate.getValue();
                            VariableReferenceExpression rightVariableReference = inPredicate.getSubquery();

                            optTrace.incrIndent(1);
                            optTrace.msg("Left var  : %s (%s)", true, leftVariableReference.getName(), leftVariableReference.getType().getDisplayName());
                            optTrace.msg("Right var : %s (%s)", true, rightVariableReference.getName(), rightVariableReference.getType().getDisplayName());
                            optTrace.decrIndent(1);
                            ++cnt;
                        }
                    }

                    if (applyNode.getCorrelation().size() > 0) {
                        optTrace.traceVariableReferenceExpressionList(applyNode.getCorrelation(), 1, "Correlations :");
                    }

                    optTrace.decrIndent(1);

                    optTrace.traceVariableReferenceExpressionList(applyNode.getOutputVariables(), 1, "Output variables :");
                    optTrace.tracePreferredPropertiesForPlanNode(applyNode, 1, "Preferred properties :");
                    optTrace.tracePlanNodeStatsEstimate(applyNode, 1, "Estimated stats :");

                    if (checkDepth()) {
                        PlanNode input = applyNode.getInput();
                        optTrace.incrIndent(1);
                        optTrace.msg("Input :", true);
                        optTrace.incrIndent(1);
                        incrementDepth();
                        input.accept(this, optTraceContext);
                        optTrace.decrIndent(2);
                        decrementDepth();

                        PlanNode subquery = applyNode.getSubquery();
                        optTrace.incrIndent(1);
                        optTrace.msg("Subquery :", true);
                        optTrace.incrIndent(1);
                        incrementDepth();
                        subquery.accept(this, optTraceContext);
                        optTrace.decrIndent(2);
                        decrementDepth();
                    }
                    else {
                        optTrace.incrIndent(1);
                        optTrace.msg("Input : ...", true);
                        optTrace.decrIndent(1);

                        PlanNode subquery = applyNode.getSubquery();
                        optTrace.incrIndent(1);
                        optTrace.msg("Subquery : ...", true);
                        optTrace.decrIndent(1);
                    }

                    break;
                }

                default: {
                    for (PlanNode child : applyNode.getSources()) {
                        incrementDepth();
                        child.accept(this, optTraceContext);
                        decrementDepth();
                    }
                }
            }

            return null;
        }

        @Override
        public PlanNode visitRemoteSource(RemoteSourceNode remoteSourceNode, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();
            List<PlanFragmentId> fragmentIds = remoteSourceNode.getSourceFragmentIds();
            boolean processed = false;

            switch (optTraceContext.visitType) {
                case BUILD_JOIN_STRING: {
                    if (fragmentIds.size() == 1) {
                        PlanFragmentId planFragmentId = fragmentIds.get(0);
                        SubPlan subPlan = optTrace.findSubPlan(planFragmentId);

                        if (subPlan != null) {
                            PlanNode fragmentRootNode = subPlan.getFragment().getRoot();

                            incrementDepth();
                            fragmentRootNode.accept(this, optTraceContext);
                            decrementDepth();
                            processed = true;
                        }
                    }

                    break;
                }

                default:
                    break;
            }

            if (!processed) {
                for (PlanFragmentId planFragmentId : fragmentIds) {
                    SubPlan subPlan = optTrace.findSubPlan(planFragmentId);

                    if (subPlan != null) {
                        PlanNode fragmentRootNode = subPlan.getFragment().getRoot();
                        incrementDepth();
                        fragmentRootNode.accept(this, optTraceContext);
                        decrementDepth();
                    }
                }
            }

            return null;
        }

        @Override
        public PlanNode visitGroupReference(GroupReference groupReference, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();

            requireNonNull(optTrace.lookUp(), "loopUp is null");
            Stream<PlanNode> planNodes;

            try {
                planNodes = optTrace.lookUp().resolveGroup(groupReference);
            }
            catch (Exception e) {
                planNodes = null;
            }

            switch (optTraceContext.visitType) {
                case PRINT: {
                    int groupId = groupReference.getGroupId();

                    optTrace.msg("Group id " + groupId + " : ", true);

                    if (planNodes != null) {
                        AtomicInteger count = new AtomicInteger(-1);
                        planNodes.forEach(member -> {
                            if (checkDepth()) {
                                optTrace.incrIndent(1);
                                optTrace.msg("Member %d :", true, count.incrementAndGet());
                                optTrace.incrIndent(1);
                                incrementDepth();
                                member.accept(this, optTraceContext);
                                optTrace.decrIndent(2);
                                decrementDepth();
                            }
                            else {
                                optTrace.incrIndent(1);
                                optTrace.msg("Member %d : ...", true, count.incrementAndGet());
                                optTrace.decrIndent(1);
                            }
                        });
                    }
                    else {
                        optTrace.incrIndent(1);
                        optTrace.msg("<no members>", true);
                        optTrace.decrIndent(1);
                    }

                    break;
                }

                default: {
                    if (planNodes != null) {
                        planNodes.forEach(member -> {
                            incrementDepth();
                            member.accept(this, optTraceContext);
                            decrementDepth();
                        });
                    }

                    break;
                }
            }

            return null;
        }

        @Override
        public PlanNode visitAggregation(AggregationNode aggregationNode, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();

            switch (optTraceContext.visitType) {
                case PRINT: {
                    Integer joinId = optTrace.getJoinId(aggregationNode);
                    optTrace.msg("Aggregation (node id " + aggregationNode.getId()
                            + ", join id " + joinId + ")", true);

                    optTrace.incrIndent(1);
                    optTrace.traceVariableReferenceExpressionList(aggregationNode.getOutputVariables(), 0, "Output variables :");
                    optTrace.tracePreferredPropertiesForPlanNode(aggregationNode, 0, "Preferred properties :");
                    optTrace.tracePlanNodeStatsEstimate(aggregationNode, 1, "Estimated stats :");

                    optTrace.msg("Distinct? : %s", true, AggregationNode.isDistinct(aggregationNode) ? "true" : "false");

                    optTrace.traceVariableReferenceExpressionList(aggregationNode.getGroupingKeys(), 0, "Grouping keys :");

                    AggregationNode.GroupingSetDescriptor groupingSets = aggregationNode.getGroupingSets();
                    if (groupingSets != null) {
                        optTrace.msg("Grouping set descriptor", true);
                        optTrace.incrIndent(1);
                        optTrace.traceVariableReferenceExpressionList(groupingSets.getGroupingKeys(), 1, "Grouping keys :");

                        Set<Integer> globalGroupingSets = groupingSets.getGlobalGroupingSets();

                        if (!globalGroupingSets.isEmpty()) {
                            optTrace.msg("Global grouping sets :", true);
                            optTrace.incrIndent(1);
                            int cnt = 0;
                            for (Integer globalGroupingSetId : globalGroupingSets) {
                                optTrace.msg("%d : %d", true, cnt, globalGroupingSetId.intValue());
                                ++cnt;
                            }
                            optTrace.decrIndent(1);
                        }

                        optTrace.decrIndent(1);
                    }

                    optTrace.msg("Has default output? : %s", true, aggregationNode.hasDefaultOutput() ? "true" : "false");

                    Map<VariableReferenceExpression, AggregationNode.Aggregation> aggregations = aggregationNode.getAggregations();
                    if (aggregations != null) {
                        optTrace.msg("Aggregations :", true);
                        optTrace.incrIndent(1);
                        int cnt = 0;
                        for (Map.Entry<VariableReferenceExpression, AggregationNode.Aggregation> aggregationMapEntry : aggregations.entrySet()) {
                            AggregationNode.Aggregation aggregation = aggregationMapEntry.getValue();

                            StringBuilder builder = new StringBuilder(format("%d : %s => %s(", cnt, aggregationMapEntry.getKey().getName(),
                                    aggregation.getCall().getDisplayName()));

                            boolean first = true;
                            for (RowExpression argument : aggregation.getArguments()) {
                                if (!first) {
                                    builder.append(" , ");
                                }

                                builder.append(format("%s", argument.toString()));

                                first = false;
                            }
                            builder.append(")");
                            optTrace.msg(builder.toString(), true);
                            optTrace.incrIndent(1);
                            optTrace.msg("Distinct? : %s", true, aggregation.isDistinct() ? "true" : "false");

                            if (aggregation.getOrderBy().isPresent()) {
                                optTrace.msg("Ordering ? : %s", true, aggregation.getOrderBy().get());
                            }

                            if (aggregation.getFilter().isPresent()) {
                                optTrace.msg("Filter ? : %s", true, aggregation.getFilter().get().toString());
                            }

                            optTrace.decrIndent(1);
                            ++cnt;
                        }
                        optTrace.decrIndent(1);
                    }

                    List<VariableReferenceExpression> preGroupedVariables = aggregationNode.getPreGroupedVariables();
                    optTrace.traceVariableReferenceExpressionList(preGroupedVariables, 1, "Pregrouped variables :");

                    Optional<VariableReferenceExpression> hashVariable = aggregationNode.getHashVariable();
                    if (hashVariable.isPresent()) {
                        optTrace.msg("Hash variable ? : %s", true, hashVariable.get().toString());
                    }

                    Optional<VariableReferenceExpression> groupIdVariable = aggregationNode.getGroupIdVariable();
                    if (groupIdVariable.isPresent()) {
                        optTrace.msg("Group id variable ? : %s", true, groupIdVariable.get().toString());
                    }

                    if (checkDepth()) {
                        PlanNode child = aggregationNode.getSource();
                        optTrace.msg("Child :", true);
                        optTrace.incrIndent(1);
                        incrementDepth();
                        child.accept(this, optTraceContext);
                        optTrace.decrIndent(2);
                        decrementDepth();
                    }
                    else {
                        optTrace.msg("Child : ...", true);
                        optTrace.decrIndent(1);
                    }

                    break;
                }

                default: {
                    for (PlanNode child : aggregationNode.getSources()) {
                        incrementDepth();
                        child.accept(this, optTraceContext);
                        decrementDepth();
                    }

                    break;
                }
            }

            return null;
        }

        @Override
        public PlanNode visitProject(ProjectNode projectNode, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();

            switch (optTraceContext.visitType) {
                case PRINT: {
                    Integer joinId = optTrace.getJoinId(projectNode);
                    optTrace.msg("Project (node id " + projectNode.getId()
                            + ", join id " + joinId + ")", true);

                    optTrace.incrIndent(1);
                    optTrace.traceVariableReferenceExpressionList(projectNode.getOutputVariables(), 0, "Output variables :");
                    optTrace.tracePreferredPropertiesForPlanNode(projectNode, 0, "Preferred properties :");
                    optTrace.tracePlanNodeStatsEstimate(projectNode, 1, "Estimated stats :");

                    Assignments assignments = projectNode.getAssignments();
                    Map<VariableReferenceExpression, RowExpression> assignmentMap = assignments.getMap();
                    optTrace.msg("Assignments :", true);
                    optTrace.incrIndent(1);
                    int cnt = 0;
                    for (Map.Entry<VariableReferenceExpression, RowExpression> assignmentMapEntry : assignmentMap.entrySet()) {
                        optTrace.msg("%d : %s => %s", true, cnt, assignmentMapEntry.getKey().getName(),
                                assignmentMapEntry.getValue().toString());
                        ++cnt;
                    }
                    optTrace.decrIndent(1);

                    optTrace.msg("Locality : %s", true, projectNode.getLocality());

                    if (projectNode.getSourceLocation().isPresent() && projectNode.getSourceLocation().get() != null) {
                        String locationStr = sourceLocationToString(projectNode.getSourceLocation().get());
                        optTrace.msg("Location : %s", true, locationStr);
                    }

                    optTrace.decrIndent(1);

                    cnt = 0;
                    optTrace.incrIndent(1);
                    for (PlanNode child : projectNode.getSources()) {
                        if (checkDepth()) {
                            optTrace.msg("Child %d :", true, cnt);
                            optTrace.incrIndent(1);
                            incrementDepth();
                            child.accept(this, optTraceContext);
                            optTrace.decrIndent(1);
                            decrementDepth();
                        }
                        else {
                            optTrace.msg("Child %d : ...", true, cnt);
                        }

                        ++cnt;
                    }
                    optTrace.decrIndent(1);

                    break;
                }

                default: {
                    for (PlanNode child : projectNode.getSources()) {
                        incrementDepth();
                        child.accept(this, optTraceContext);
                        decrementDepth();
                    }

                    break;
                }
            }

            return null;
        }

        @Override
        public PlanNode visitFilter(FilterNode filterNode, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();

            switch (optTraceContext.visitType) {
                case PRINT: {
                    Integer joinId = optTrace.getJoinId(filterNode);
                    optTrace.msg("Filter (node id " + filterNode.getId()
                            + ", join id " + joinId + ")", true);

                    optTrace.traceVariableReferenceExpressionList(filterNode.getOutputVariables(), 1, "Output variables :");
                    optTrace.tracePreferredPropertiesForPlanNode(filterNode, 1, "Preferred properties :");
                    optTrace.tracePlanNodeStatsEstimate(filterNode, 1, "Estimated stats :");

                    optTrace.incrIndent(1);
                    optTrace.msg("Predicate :", true);
                    optTrace.incrIndent(1);
                    optTrace.msg(filterNode.getPredicate().toString(), true, null);
                    optTrace.decrIndent(2);

                    int cnt = 0;
                    optTrace.incrIndent(1);
                    for (PlanNode child : filterNode.getSources()) {
                        if (checkDepth()) {
                            optTrace.msg("Child %d :", true, cnt);
                            optTrace.incrIndent(1);
                            incrementDepth();
                            child.accept(this, optTraceContext);
                            optTrace.decrIndent(1);
                            decrementDepth();
                        }
                        else {
                            optTrace.msg("Child %d : ...", true, cnt);
                        }
                        ++cnt;
                    }
                    optTrace.decrIndent(1);

                    break;
                }

                default: {
                    for (PlanNode child : filterNode.getSources()) {
                        incrementDepth();
                        child.accept(this, optTraceContext);
                        decrementDepth();
                    }

                    break;
                }
            }

            return null;
        }

        @Override
        public PlanNode visitExchange(ExchangeNode exchange, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();

            switch (optTraceContext.visitType) {
                case PRINT: {
                    ExchangeNode.Type type = exchange.getType();
                    ExchangeNode.Scope scope = exchange.getScope();
                    PartitioningScheme partitioningScheme = exchange.getPartitioningScheme();

                    optTrace.msg("ExchangeNode[%s] (node id %s)", true, exchange.getType(), exchange.getId());
                    optTrace.traceVariableReferenceExpressionList(exchange.getOutputVariables(), 1, "Output variables :");
                    optTrace.tracePreferredPropertiesForPlanNode(exchange, 1, "Preferred properties :");
                    optTrace.tracePlanNodeStatsEstimate(exchange, 1, "Estimated stats :");
                    optTrace.tracePartitioningScheme(exchange.getPartitioningScheme(), 1, "Partitioning scheme :");
                    optTrace.traceOrderingScheme(exchange.getOrderingScheme(), 1, "Ordering scheme :");
                    optTrace.incrIndent(1);

                    optTrace.msg("Inputs :", true);
                    optTrace.incrIndent(1);
                    int cnt = 0;
                    for (List<VariableReferenceExpression> input : exchange.getInputs()) {
                        optTrace.msg("%d : ", true, cnt);
                        optTrace.traceVariableReferenceExpressionList(input, 1, null);
                    }
                    optTrace.decrIndent(1);

                    optTrace.msg("Scope : %s", true, scope.toString());
                    optTrace.msg("Ensure source ordering? : %s", true, exchange.isEnsureSourceOrdering());
                    optTrace.decrIndent(1);

                    int childId = 0;
                    for (PlanNode child : exchange.getSources()) {
                        if (checkDepth()) {
                            optTrace.incrIndent(1);
                            optTrace.msg("Child %d :", true, childId);
                            optTrace.incrIndent(1);
                            incrementDepth();
                            child.accept(this, optTraceContext);
                            optTrace.decrIndent(2);
                            decrementDepth();
                        }
                        else {
                            optTrace.incrIndent(1);
                            optTrace.msg("Child %d : ...", true, childId);
                            optTrace.decrIndent(1);
                        }

                        ++childId;
                    }

                    break;
                }

                default: {
                    for (PlanNode child : exchange.getSources()) {
                        incrementDepth();
                        child.accept(this, optTraceContext);
                        decrementDepth();
                    }
                }
            }

            return null;
        }

        private static String formatHash(Optional<VariableReferenceExpression>... hashes)
        {
            List<VariableReferenceExpression> variables = stream(hashes)
                    .filter(Optional::isPresent)
                    .map(Optional::get)
                    .collect(toList());

            if (variables.isEmpty()) {
                return "<empty>";
            }

            return "[" + Joiner.on(", ").join(variables) + "]";
        }

        @Override
        public PlanNode visitJoin(JoinNode join, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();

            switch (optTraceContext.visitType) {
                case PRINT: {
                    Integer traceId = optTrace.getTraceId(join);
                    Integer joinId = optTrace.getJoinId(join);

                    List<Expression> joinExpressions = new ArrayList<>();
                    for (JoinNode.EquiJoinClause clause : join.getCriteria()) {
                        joinExpressions.add(JoinNodeUtils.toExpression(clause));
                    }

                    String criteria = Joiner.on(" AND ").join(joinExpressions);

                    Pair<String, String> joinStrings = optTrace.getJoinStrings(join);
                    requireNonNull(joinStrings, "join strings are null");

                    optTrace.msg(join.getType().getJoinLabel() + " (node id " + join.getId()
                            + " , join id " + joinId + " , trace id " + traceId + ")", true);
                    optTrace.traceVariableReferenceExpressionList(join.getOutputVariables(), 1, "Output variables :");
                    optTrace.tracePreferredPropertiesForPlanNode(join, 1, "Preferred properties :");
                    optTrace.tracePlanNodeStatsEstimate(join, 1, "Estimated stats :");

                    optTrace.incrIndent(1);
                    optTrace.msg("Join string : " + joinStrings.getKey() + ") , hash code " + joinStrings.getKey().hashCode(), true);

                    optTrace.msg("Constraint : " + joinStrings.getValue() + ")", true);

                    Optional<JoinNode.DistributionType> distType = join.getDistributionType();

                    optTrace.msg("Criteria : %s", true, criteria);

                    if (join.getFilter().isPresent()) {
                        optTrace.msg("Filter : %s", true, join.getFilter().get().toString());
                    }

                    if (join.getCriteria() != null && join.getCriteria().size() > 0) {
                        List<VariableReferenceExpression> leftVariables = join.getCriteria().stream()
                                .map(JoinNode.EquiJoinClause::getLeft)
                                .collect(toImmutableList());
                        List<VariableReferenceExpression> rightVariables = join.getCriteria().stream()
                                .map(JoinNode.EquiJoinClause::getRight)
                                .collect(toImmutableList());

                        optTrace.traceVariableReferenceExpressionList(leftVariables, 1, "Left criteria variables :");
                        optTrace.traceVariableReferenceExpressionList(rightVariables, 1, "Right criteria variables :");
                    }

                    String formattedHash = formatHash(join.getLeftHashVariable());
                    optTrace.msg("Left hash var. : %s", true, formattedHash);
                    formattedHash = formatHash(join.getRightHashVariable());
                    optTrace.msg("Right hash var. : %s", true, formattedHash);
                    distType.ifPresent(dist -> optTrace.msg("Distribution type : %s", true, dist.name()));

                    optTrace.decrIndent(1);

                    if (checkDepth()) {
                        optTrace.incrIndent(1);
                        optTrace.msg("Left input :", true);
                        optTrace.incrIndent(1);
                        incrementDepth();
                        join.getLeft().accept(this, optTraceContext);
                        optTrace.decrIndent(2);
                        decrementDepth();
                    }
                    else {
                        optTrace.incrIndent(1);
                        optTrace.msg("Left input : ...", true);
                        optTrace.decrIndent(1);
                    }

                    if (checkDepth()) {
                        optTrace.incrIndent(1);
                        optTrace.msg("Right input :", true);
                        optTrace.incrIndent(1);
                        incrementDepth();
                        join.getRight().accept(this, optTraceContext);
                        optTrace.decrIndent(2);
                        decrementDepth();
                    }
                    else {
                        optTrace.incrIndent(1);
                        optTrace.msg("Right input : ...", true);
                        optTrace.decrIndent(1);
                    }

                    break;
                }

                case CNT_JOINS:
                    ++(optTraceContext.joinCnt);
                    break;

                case BUILD_JOIN_STRING: {
                    if (optTraceContext.joinString == null) {
                        optTraceContext.joinString = new String("(");
                    }
                    else {
                        optTraceContext.joinString = optTraceContext.joinString + "(";
                    }

                    incrementDepth();
                    join.getLeft().accept(this, optTraceContext);

                    if (join.isCrossJoin()) {
                        optTraceContext.joinString = optTraceContext.joinString + " CROSS ";
                    }
                    else {
                        optTraceContext.joinString = optTraceContext.joinString + " " + join.getType() + " ";
                    }

                    join.getRight().accept(this, optTraceContext);
                    decrementDepth();

                    Optional<JoinNode.DistributionType> distType = join.getDistributionType();

                    optTraceContext.joinString = optTraceContext.joinString + ")";

                    String distStr = null;
                    if (distType.isPresent()) {
                        JoinNode.DistributionType joinDistType = distType.get();
                        switch (joinDistType) {
                            case PARTITIONED:
                                distStr = new String("[P]");
                                break;
                            case REPLICATED:
                                distStr = new String("[R]");
                                break;
                            default:
                                distStr = new String("[?]");
                                break;
                        }

                        optTraceContext.joinString = optTraceContext.joinString + " " + distStr;
                    }

                    break;
                }

                default: {
                    for (PlanNode child : join.getSources()) {
                        incrementDepth();
                        child.accept(this, optTraceContext);
                        decrementDepth();
                    }
                }
            }

            return null;
        }

        @Override
        public PlanNode visitSemiJoin(SemiJoinNode join, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();

            switch (optTraceContext.visitType) {
                case PRINT: {
                    Integer traceId = optTrace.getTraceId(join);
                    Integer joinId = optTrace.getJoinId(join);

                    optTrace.msg("SemiJoin (node id " + join.getId() +
                            " , join id " + traceId + ")", true);

                    optTrace.traceVariableReferenceExpressionList(join.getOutputVariables(), 1, "Output variables :");
                    optTrace.tracePreferredPropertiesForPlanNode(join, 1, "Preferred properties :");
                    optTrace.tracePlanNodeStatsEstimate(join, 1, "Estimated stats :");

                    Pair<String, String> joinStrings = optTrace.getJoinStrings(join);
                    requireNonNull(joinStrings, "join strings are null");

                    optTrace.incrIndent(1);

                    optTrace.msg("Join string : " + joinStrings.getKey() + ")", true);

                    optTrace.msg("Constraint : " + joinStrings.getValue() + ")", true);

                    optTrace.msg("Source join var           : %s (%s)", true, join.getSourceJoinVariable().getName(),
                            join.getSourceJoinVariable().getType().getDisplayName());

                    optTrace.msg("Filtering source join var : %s (%s)", true, join.getFilteringSourceJoinVariable().getName(),
                            join.getFilteringSourceJoinVariable().getType().getDisplayName());

                    Optional<SemiJoinNode.DistributionType> distType = join.getDistributionType();

                    distType.ifPresent(dist -> optTrace.msg("Distribution type : %s", true, dist.name()));

                    optTrace.decrIndent(1);

                    if (checkDepth()) {
                        optTrace.incrIndent(1);
                        incrementDepth();
                        optTrace.msg("Probe :", true);
                        optTrace.incrIndent(1);
                        join.getProbe().accept(this, optTraceContext);
                        optTrace.decrIndent(2);
                        decrementDepth();
                    }
                    else {
                        optTrace.incrIndent(1);
                        optTrace.msg("Probe : ...", true);
                        optTrace.decrIndent(1);
                    }

                    if (checkDepth()) {
                        optTrace.incrIndent(1);
                        optTrace.msg("Build :", true);
                        optTrace.incrIndent(1);
                        incrementDepth();
                        join.getBuild().accept(this, optTraceContext);
                        optTrace.decrIndent(2);
                        decrementDepth();
                    }
                    else {
                        optTrace.incrIndent(1);
                        optTrace.msg("Build : ...", true);
                        optTrace.decrIndent(1);
                    }

                    break;
                }

                case CNT_JOINS:
                    ++(optTraceContext.joinCnt);
                    break;

                case BUILD_JOIN_STRING: {
                    if (optTraceContext.joinString == null) {
                        optTraceContext.joinString = new String("(");
                    }
                    else {
                        optTraceContext.joinString = optTraceContext.joinString + "(";
                    }

                    incrementDepth();
                    join.getProbe().accept(this, optTraceContext);
                    optTraceContext.joinString = optTraceContext.joinString + " SEMI ";
                    join.getBuild().accept(this, optTraceContext);
                    decrementDepth();

                    optTraceContext.joinString = optTraceContext.joinString + ")";

                    break;
                }

                default: {
                    for (PlanNode child : join.getSources()) {
                        incrementDepth();
                        child.accept(this, optTraceContext);
                        decrementDepth();
                    }
                }
            }

            return null;
        }

        @Override
        public PlanNode visitTableScan(TableScanNode tableScan, OptTraceContext optTraceContext)
        {
            OptTrace optTrace = optTraceContext.optTrace();
            ++(optTraceContext.tableCnt);

            switch (optTraceContext.visitType) {
                case PRINT: {
                    Integer joinId = optTrace.getJoinId(tableScan);

                    if (joinId == null) {
                        throw new PrestoException(GENERIC_INTERNAL_ERROR, format("Could not find join id : %s (node id ", tableName(tableScan, optTrace)) +
                                tableScan.getId() + ")");
                    }

                    ActualProperties actualProperties = PropertyDerivations.deriveProperties(tableScan, null, optTrace.metadata, optTrace.session,
                            optTrace.types, optTrace.parser);
                    optTrace.traceActualProperties(actualProperties, 0, "Actual properties :");

                    if (tableScan.getSourceLocation().isPresent()) {
                        optTrace.msg(tableScan.getClass().getSimpleName() + " (" + tableName(tableScan, optTrace) + " , " +
                                sourceLocationToString(tableScan.getSourceLocation().get()) +
                                " , node id " + tableScan.getId() + " , join id " + joinId + ")", true);
                    }
                    else {
                        optTrace.msg(tableScan.getClass().getSimpleName() + " (" + tableName(tableScan, optTrace) + " , node id "
                                + tableScan.getId() + " , join id " + joinId + ")", true);
                    }

                    optTrace.traceVariableReferenceExpressionList(tableScan.getOutputVariables(), 1, "Output variables :");
                    optTrace.tracePreferredPropertiesForPlanNode(tableScan, 1, "Preferred properties :");
                    optTrace.tracePlanNodeStatsEstimate(tableScan, 1, "Estimated stats :");

                    if (tableScan.getSourceLocation().isPresent() && tableScan.getSourceLocation().get() != null) {
                        String locationStr = sourceLocationToString(tableScan.getSourceLocation().get());
                        optTrace.msg("Location : %s", true, locationStr);
                    }

                    break;
                }

                case FIND_TABLES: {
                    optTraceContext.addTableScan(tableScan);
                    break;
                }

                case CNT_TABLES: {
                    break;
                }

                case BUILD_JOIN_STRING: {
                    if (optTraceContext.joinString == null) {
                        optTraceContext.joinString = new String(tableName(tableScan, optTrace));
                    }
                    else {
                        optTraceContext.joinString = optTraceContext.joinString + tableName(tableScan, optTrace);
                    }
                }

                default:
            }

            return null;
        }
    }

    private static String tableName(TableScanNode tableScanNode, OptTrace optTrace)
    {
        String str = null;

        if (optTrace != null && optTrace.locationToTableOrAliasNameMap != null &&
                tableScanNode.getSourceLocation().isPresent()) {
            String locationString = sourceLocationToString(tableScanNode.getSourceLocation().get());

            if (optTrace.locationToTableOrAliasNameMap.containsKey(locationString)) {
                List<String> nameOrAliasList = optTrace.locationToTableOrAliasNameMap.get(locationString).stream().collect(toList());
                checkArgument(nameOrAliasList.size() == 1, format("multiple (or zero) table name/aliases at location %s", locationString));

                str = nameOrAliasList.get(0);
            }
        }

        if (str == null) {
            str = tableScanNode.getTable().getConnectorHandle().toString();
            String token = new String("tableName=");
            int startPos = str.indexOf(token);
            if (startPos != -1) {
                startPos += token.length();
                int endPos = str.indexOf(",", startPos);

                if (endPos != -1) {
                    str = str.substring(startPos, endPos);
                }
            }
        }

        return str;
    }

    public static void doIndent(BufferedWriter bufferedWriter, int indentCnt)
    {
        try {
            for (int i = 0; i < indentCnt; ++i) {
                bufferedWriter.write(" ");
            }
        }
        catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private String tableName(int groupId)
    {
        String name = null;
        if (memo != null) {
            PlanNode planNode = memo.getNode(groupId);

            if (planNode instanceof TableScanNode) {
                TableScanNode tableScan = (TableScanNode) planNode;
                name = tableName(tableScan, this);
            }
        }

        return name;
    }

    public void tracePartition(Set<Integer> partition, String msgString, Object... args)
    {
        requireNonNull(partition, "partition is null");

        StringBuilder partMsgBuilderIds = new StringBuilder();

        if (msgString != null) {
            partMsgBuilderIds.append(String.format(msgString, args));
        }

        partMsgBuilderIds.append("[");

        boolean first = true;
        boolean foundName = false;
        for (int group : partition) {
            if (!first) {
                partMsgBuilderIds.append(" , ");
            }

            partMsgBuilderIds.append(String.format("%s", group));

            first = false;
        }

        partMsgBuilderIds.append("]");

        msg(partMsgBuilderIds.toString(), true);
    }

    public void traceJoinSources(Set<PlanNode> sources, int indentCnt, String msgString, Object... args)
    {
        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true, args);
            incrIndent(1);
        }

        int cnt = 0;
        for (PlanNode source : sources) {
            int joinId = getJoinId(source);
            String sourceStr = null;

            String nodeStr;

            if (source instanceof TableScanNode || source instanceof JoinNode || source instanceof SemiJoinNode) {
                Pair<String, String> joinStrings = getJoinStrings(source);
                requireNonNull(joinStrings, "join strings are null");

                nodeStr = joinStrings.getKey();
            }
            else {
                LinkedHashSet<TableScanNode> tableScans = getTableScans(source);

                if (tableScans != null && tableScans.size() > 0) {
                    nodeStr = tableScansToString(tableScans);
                }
                else {
                    nodeStr = new String(source.getClass().getSimpleName() + " " + source.getId().getId());
                }
            }

            if (source instanceof GroupReference) {
                GroupReference groupReference = (GroupReference) source;
                Stream<PlanNode> planNodes = lookUp.resolveGroup(groupReference);
                Optional<PlanNode> groupPlanNode = planNodes.findFirst();
                if (groupPlanNode.isPresent()) {
                    source = groupPlanNode.get();
                }
            }

            String sourceSimpleName;
            if (source instanceof JoinNode) {
                JoinNode joinNode = (JoinNode) source;
                sourceSimpleName = joinNode.getType().name();
            }
            else {
                sourceSimpleName = source.getClass().getSimpleName();
            }

            if (joinId != -1) {
                sourceStr = "Source %d : " + sourceSimpleName + " " + nodeStr + format(" (node id %s , join id %d)",
                        source.getId(), joinId);
            }
            else {
                throw new PrestoException(GENERIC_INTERNAL_ERROR, format("join id lookup failed"));
            }

            msg(sourceStr, true, cnt);
            ++cnt;
        }

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void tracePlanCostEstimate(PlanCostEstimate planCostEstimate, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(planCostEstimate, "node is null");

        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true, args);
            incrIndent(1);
        }

        if (planCostEstimate == PlanCostEstimate.infinite()) {
            msg("<infinite>", true);
        }
        else if (planCostEstimate == PlanCostEstimate.unknown()) {
            msg("<unknown>", true);
        }
        else if (planCostEstimate == PlanCostEstimate.zero()) {
            msg("<zero>", true);
        }
        else {
            msg("Cpu : %.3f , Network : %.3f , Max. mem. : %.3f", true, planCostEstimate.getCpuCost(),
                    planCostEstimate.getNetworkCost(),
                    planCostEstimate.getMaxMemory());
        }

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void tracePlanNodeStatsEstimate(PlanNodeStatsEstimate planNodeStatsEstimate, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(planNodeStatsEstimate, "stats node estimate is null");

        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true, args);
            incrIndent(1);
        }

        if (planNodeStatsEstimate == PlanNodeStatsEstimate.unknown()) {
            msg("<unknown>", true);
        }
        else {
            msg("Row count : %.0f, confident? %s", true, planNodeStatsEstimate.getOutputRowCount(),
                    planNodeStatsEstimate.isConfident() ? "true" : "false");
        }

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void traceJoinConstraint(PlanNode planNode, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(planNode, "node is null");

        if (msgString != null) {
            incrIndent(indentCnt);

            msg(msgString, true, args);
        }

        incrIndent(1);
        JoinConstraintNode joinConstraint = joinConstraintNode(planNode, null, false);

        if (joinConstraint != null) {
            String joinConstraintString = null;
            Long joinId = joinConstraint.joinId();
            if (joinId == null) {
                PlanNode source = joinConstraint.getSourceNode();
                requireNonNull(source, "source of join constraint is null");
                joinId = Long.valueOf(getJoinId(source));
                requireNonNull(joinId, "join id is null");
            }

            joinConstraintString = joinConstraint.joinConstraintString();
            msg(joinConstraintString + " (join id %d)", true, joinId.intValue());
        }
        else {
            msg("<no join>", true);
        }

        decrIndent(1);

        if (msgString != null) {
            decrIndent(indentCnt);
        }
    }

    public void traceEnumeratedJoins(PlanNode root, CostProvider costProvider, StatsProvider statsProvider, int indentCnt,
            String msgString, Object... args)
    {
        requireNonNull(root, "root is null");
        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true, args);
            incrIndent(1);
        }

        PlanNodeTableScanCntComparator compare = new PlanNodeTableScanCntComparator(this);
        LinkedHashSet<TableScanNode> tableScans = getTableScans(root);

        if (tableScans != null) {
            ArrayList<TableScanNode> tableScansArray = new ArrayList<>(tableScans);
            tableScansArray.sort(compare);

            msg("Table scans :", true);
            incrIndent(1);
            int cnt = 0;
            for (TableScanNode tableScanNode : tableScansArray) {
                int joinId = getJoinId(tableScanNode);
                String sourceStr = null;
                Pair<String, String> joinStrings = getJoinStrings(tableScanNode);
                requireNonNull(joinStrings, "join strings are null");

                if (joinId != -1) {
                    sourceStr = "Table scan %d : " + tableScanNode.getClass().getSimpleName() + " " + joinStrings.getKey() + format(" (node id %s , join id %d)",
                            tableScanNode.getId(), joinId);
                }
                else {
                    throw new PrestoException(GENERIC_INTERNAL_ERROR, format("join id lookup failed"));
                }

                msg(sourceStr, true, cnt);

                if (costProvider != null) {
                    PlanCostEstimate planCostEstimate = costProvider.getCost(tableScanNode);
                    tracePlanCostEstimate(planCostEstimate, 1, "Estimated cost :");
                }

                if (statsProvider != null) {
                    PlanNodeStatsEstimate planNodeStatsEstimate = statsProvider.getStats(tableScanNode);
                    tracePlanNodeStatsEstimate(planNodeStatsEstimate, 1, "Estimated stats :");
                }

                ++cnt;
            }

            decrIndent(1);
        }
        else {
            msg("No table scans.", true);
        }

        Collections.sort(enumeratedJoins, compare);

        msg("Joins :", true);
        incrIndent(1);
        int cnt = 0;
        for (JoinNode joinNode : enumeratedJoins) {
            Integer joinId = getJoinId(joinNode);
            requireNonNull(joinId, "join id is null");
            Pair<String, String> joinStrings = getJoinStrings(joinNode);
            PruneReason pruneReason = isPruned(joinId);

            if (pruneReason != null) {
                msg("%d : %s , join id %d, hash code %d (** PRUNED BY %s **)", true, cnt,
                        joinStrings.getValue(), joinId.intValue(), joinStrings.getKey().hashCode(), pruneReason.getString().toUpperCase());
            }
            else {
                msg("%d : %s , join id %d, hash code %d (** ACCEPTED **)", true, cnt, joinStrings.getValue(), joinId.intValue(),
                        joinStrings.getKey().hashCode());
            }

            msg("    %s", true, joinStrings.getKey());

            if (costProvider != null) {
                PlanCostEstimate planCostEstimate = costProvider.getCost(joinNode);
                tracePlanCostEstimate(planCostEstimate, 1, "Estimated cost :");
            }

            if (statsProvider != null) {
                PlanNodeStatsEstimate planNodeStatsEstimate = statsProvider.getStats(joinNode);
                tracePlanNodeStatsEstimate(planNodeStatsEstimate, 1, "Estimated stats :");
            }

            ++cnt;
        }

        decrIndent(1);

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void tracePartitioning(Partitioning partitioning, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(partitioning, "partitioning is null");

        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true);
            incrIndent(1);
        }

        PartitioningHandle handle = partitioning.getHandle();

        msg("Single node? %s", true, handle.getConnectorHandle().isSingleNode() ? "true" : "false");
        msg("Coordinator only? %s", true, handle.getConnectorHandle().isCoordinatorOnly() ? "true" : "false");

        msg("Arguments :", true);
        incrIndent(1);
        List<RowExpression> arguments = partitioning.getArguments();
        int cnt = 0;
        for (RowExpression arg : arguments) {
            msg("%d : %s", true, cnt, arg.toString());
            ++cnt;
        }
        decrIndent(1);

        Set<VariableReferenceExpression> varRefs = partitioning.getVariableReferences();
        traceVariableReferenceExpressionList(varRefs.stream().collect(toList()), 1, "Variable references :");

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void traceOrderingScheme(Optional<OrderingScheme> orderingSchemeParam, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(orderingSchemeParam, "ordering scheme is null");
        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true);
            incrIndent(1);
        }

        msg("Orderings :", true);

        incrIndent(1);
        if (orderingSchemeParam.isPresent()) {
            OrderingScheme orderingScheme = orderingSchemeParam.get();

            int cnt = 0;
            for (Ordering ordering : orderingScheme.getOrderBy()) {
                msg("%d : %s %s", true, cnt, ordering.getVariable().getName(), ordering.getSortOrder());
                ++cnt;
            }
        }
        else {
            msg("<not present>", true);
        }
        decrIndent(1);

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void tracePartitioningScheme(PartitioningScheme partitioningScheme, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(partitioningScheme, "partitioning scheme is null");

        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true);
            incrIndent(1);
        }

        tracePartitioning(partitioningScheme.getPartitioning(), 0, "Partitioning :");

        traceVariableReferenceExpressionList(partitioningScheme.getOutputLayout(), 0, "Output layout :");

        Optional<VariableReferenceExpression> hashColumn = partitioningScheme.getHashColumn();

        if (hashColumn.isPresent()) {
            msg("Hash column : %s", true, hashColumn.get().getName());
        }
        else {
            msg("Hash column : <not present>", true);
        }

        msg("Replicate nulls and any : %s", true, partitioningScheme.isReplicateNullsAndAny() ? "true" : "false");

        if (partitioningScheme.getBucketToPartition().isPresent()) {
            msg("Bucket to partition : %s", true, partitioningScheme.getBucketToPartition().get().toString());
        }

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void traceVariableReferenceExpressionList(List<VariableReferenceExpression> varList, int indentCnt, String msgString, Object... args)
    {
        int cnt = 0;

        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true);
            incrIndent(1);
        }

        if (varList != null) {
            for (VariableReferenceExpression var : varList) {
                if (var.getSourceLocation().isPresent()) {
                    String locationString = var.getSourceLocation().get().toString();

                    String tableOrAliasName = null;
                    List<String> tableAliasNameList = null;
                    if (locationToTableOrAliasNameMap.containsKey(locationString)) {
                        tableAliasNameList = locationToTableOrAliasNameMap.get(locationString).stream().collect(toList());

                        checkArgument(tableAliasNameList.size() == 1, format("multiple (or zero) table name/aliases at location %s", locationString));

                        tableOrAliasName = tableAliasNameList.get(0);
                    }

                    if (tableOrAliasName != null) {
                        msg("%d : %s (%s, %s, %s)", true, cnt, var.getName(), tableOrAliasName, locationString, var.getType().getDisplayName());
                    }
                    else {
                        msg("%d : %s (%s, %s)", true, cnt, var.getName(), locationString, var.getType().getDisplayName());
                    }
                }
                else {
                    msg("%d : %s (%s)", true, cnt, var.getName(), var.getType().getDisplayName());
                }

                ++cnt;
            }
        }
        else {
            msg("<null>", true);
        }

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void tracePartitioningProperties(PreferredProperties.PartitioningProperties partitioningProperties, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(partitioningProperties, "partitioning properties is null");

        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true, args);
            incrIndent(1);
        }

        traceVariableReferenceExpressionList(partitioningProperties.getPartitioningColumns().stream().collect(toList()), 0,
                "Partitioning columns :");

        msg("Partitioning :", true);
        incrIndent(1);

        if (partitioningProperties.getPartitioning().isPresent()) {
            tracePartitioning(partitioningProperties.getPartitioning().get(), 0, null);
        }
        else {
            msg("<not present>", true);
        }

        msg("Replicate nulls and any : %s", true, partitioningProperties.isNullsAndAnyReplicated() ? "true" : "false");
        decrIndent(1);

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void tracePreferredProperties(PreferredProperties preferredProperties, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(preferredProperties, "plan node is null");

        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true, args);
            incrIndent(1);
        }

        msg("Global properties :", true);
        incrIndent(1);
        Optional<PreferredProperties.Global> globalPropertiesOpt = preferredProperties.getGlobalProperties();
        if (globalPropertiesOpt.isPresent()) {
            PreferredProperties.Global globalProperties = globalPropertiesOpt.get();
            msg("Distributed? : %s", true, globalProperties.isDistributed() ? "true" : "false");
            msg("Partitioning properties? :", true);
            incrIndent(1);
            if (globalProperties.getPartitioningProperties().isPresent()) {
                tracePartitioningProperties(globalProperties.getPartitioningProperties().get(), 0, null);
            }
            else {
                msg("<not present>", true);
            }
            decrIndent(1);
        }
        else {
            msg("<not present>", true);
        }

        decrIndent(1);

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void tracePreferredPropertiesForPlanNode(PlanNode planNode, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(planNode, "plan node is null");

        PreferredProperties preferredProperties = planNodeIdToPreferredPropertiesMap.get(planNode.getId().getId());

        if (preferredProperties != null) {
            tracePreferredProperties(preferredProperties, indentCnt, msgString, args);
        }
    }

    public void traceActualProperties(ActualProperties actualProperties, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(actualProperties, "plan node is null");

        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true, args);
            incrIndent(1);
        }

        Optional<Partitioning> nodePartitioning = actualProperties.getNodePartitioning();

        msg("Node partitioning :", true);
        incrIndent(1);

        if (nodePartitioning.isPresent()) {
            tracePartitioning(nodePartitioning.get(), 0, null);
        }
        else {
            msg("<not present>", true);
        }

        msg("Single node? : %s", true, actualProperties.isSingleNode() ? "true" : "false");
        msg("Coordinator only? : %s", true, actualProperties.isCoordinatorOnly() ? "true" : "false");
        msg("Replicate nulls and any : %s", true, actualProperties.isNullsAndAnyReplicated() ? "true" : "false");

        decrIndent(1);

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void traceActualPropertiesForPlanNode(PlanNode planNode, int indentCnt, String msgString, Object... args)
    {
        requireNonNull(planNode, "plan node is null");

        ActualProperties actualProperties = planNodeIdToActualPropertiesMap.get(planNode.getId().getId());

        if (actualProperties != null) {
            traceActualProperties(actualProperties, indentCnt, msgString, args);
        }
    }

    public void traceJoinIdMap(int indentCnt, String msgString, Object... args)
    {
        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true, args);
            incrIndent(1);
        }

        ArrayList<Map.Entry<String, Integer>> joinIdList = new ArrayList<Map.Entry<String, Integer>>(joinIdMap.entrySet());

        Collections.sort(joinIdList, Comparator.comparingInt(Map.Entry::getValue));

        int cnt = 0;
        for (Map.Entry<String, Integer> entry : joinIdList) {
            String lookUpString = entry.getKey();
            Integer joinId = entry.getValue();
            msg("%d : join id %d <= %s", true, cnt, joinId, lookUpString);
            ++cnt;
        }

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void tracePlanNode(PlanNode node, int indentCnt, String msgString, Object... args)
    {
        tracePlanNode(node, indentCnt, msgString, -1, args);
    }

    public void traceMemo()
    {
        memo.trace(bufferedWriter, indent);
    }

    public void tracePlanNode(PlanNode node, int indentCnt, String msgString, int maxDepth, Object... args)
    {
        requireNonNull(node, "node is null");

        incrIndent(indentCnt);
        if (msgString != null) {
            msg(msgString, true, args);
            incrIndent(1);
        }

        OptTraceContext optTraceContext = new OptTraceContext(this, VisitType.PRINT);
        node.accept(new OptTracePlanVisitor(maxDepth), optTraceContext);

        if (msgString != null) {
            decrIndent(1);
        }

        decrIndent(indentCnt);
    }

    public void incrIndent(int indentCnt)
    {
        indent += incrIndent * indentCnt;
    }

    public void decrIndent(int indentCnt)
    {
        indent -= incrIndent * indentCnt;
    }

    public void msg(String msgString, boolean eol, Object... args)
    {
        try {
            doIndent(bufferedWriter, indent);

            if (args != null) {
                bufferedWriter.write(String.format(msgString, args));
            }
            else {
                bufferedWriter.write(msgString);
            }

            bufferedWriter.write(" (UID " + nextUid() + ")");

            if (eol) {
                bufferedWriter.newLine();
            }
            bufferedWriter.flush();
        }
        catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public void msgNoIndent(String msgString, boolean eol, Object... args)
    {
        try {
            if (args != null) {
                bufferedWriter.write(String.format(msgString, args));
            }
            else {
                bufferedWriter.write(msgString);
            }

            bufferedWriter.write(" (UID " + nextUid() + ")");

            if (eol) {
                bufferedWriter.newLine();
            }
            bufferedWriter.flush();
        }
        catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    protected void finalize()
    {
        if (this.bufferedWriter != null) {
            try {
                bufferedWriter.flush();
                bufferedWriter.close();
            }
            catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }
}
