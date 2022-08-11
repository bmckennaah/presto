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

import com.facebook.presto.spi.PrestoException;
import com.facebook.presto.spi.plan.PlanNode;
import com.facebook.presto.spi.plan.TableScanNode;
import com.facebook.presto.sql.planner.plan.JoinNode;
import com.facebook.presto.sql.planner.plan.SemiJoinNode;
import com.google.common.collect.Multimap;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static com.facebook.presto.spi.StandardErrorCode.GENERIC_INTERNAL_ERROR;
import static com.google.common.base.Preconditions.checkArgument;
import static java.lang.String.format;
import static java.util.Objects.requireNonNull;

class JoinConstraintNode
{
    private Long id;
    private ArrayList<JoinConstraintNode> children;
    private String joinConstraintString;
    ArrayList<Long> idSet;
    ArrayList<Long> baseIdSet;
    PlanNode sourceNode;
    JoinNode.DistributionType joinDistType;
    boolean isRoot;
    String name;
    ArrayList<String> partitioning;
    ConstraintType constraintType;

    public enum ConstraintCompare
    {
        NOT_APPLICABLE("not applicable"),
        TRUE("true"),
        FALSE("false");

        private String string;

        ConstraintCompare(String stringRep)
        {
            this.string = stringRep;
        }

        public String getString()
        {
            return string;
        }
    }

    public enum ConstraintType
    {
        JOIN("JOIN"),
        CARD("CARD");

        private String string;

        ConstraintType(String stringRep)
        {
            this.string = stringRep;
        }

        public String getString()
        {
            return string;
        }
    }

    public JoinConstraintNode(TableScanNode tableScan, Long joinIdParam, String nameParam, ConstraintType constraintTypeParam)
    {
        id = joinIdParam;
        children = null;
        joinConstraintString = null;
        idSet = new ArrayList<Long>();
        baseIdSet = null;

        if (id != null) {
            idSet.add(id);
        }

        sourceNode = tableScan;
        joinDistType = null;
        isRoot = true;
        name = nameParam;
        partitioning = null;
        constraintType = constraintTypeParam;
    }

    public JoinConstraintNode(Long joinIdParam, PlanNode sourceNodeParam, ConstraintType constraintTypeParam)
    {
        id = joinIdParam;
        children = null;
        joinConstraintString = null;
        idSet = new ArrayList<Long>();
        baseIdSet = null;
        idSet.add(id);
        sourceNode = sourceNodeParam;
        joinDistType = null;
        isRoot = true;
        name = null;
        partitioning = null;
        constraintType = constraintTypeParam;
    }

    public JoinConstraintNode(ConstraintType constraintTypeParam)
    {
        id = null;
        children = null;
        joinConstraintString = null;
        idSet = new ArrayList<Long>();
        baseIdSet = null;
        sourceNode = null;
        joinDistType = null;
        isRoot = true;
        name = null;
        partitioning = null;
        constraintType = constraintTypeParam;
    }

    public JoinConstraintNode(ArrayList<JoinConstraintNode> children, ConstraintType constraintTypeParam)
    {
        id = null;
        idSet = new ArrayList<Long>();
        baseIdSet = null;
        for (JoinConstraintNode child : children) {
            appendChild(child);
        }

        joinConstraintString = null;
        sourceNode = null;
        joinDistType = null;
        isRoot = true;
        name = null;
        partitioning = null;
        constraintType = constraintTypeParam;
    }

    public ArrayList<Long> baseIdSet()
    {
        if (baseIdSet == null) {
            baseIdSet = new ArrayList<Long>();
            if (children == null || children.size() == 0) {
                if (id != null) {
                    baseIdSet.add(id);
                }
            }
            else {
                int childId = 0;
                for (JoinConstraintNode child : children) {
                    if (constraintType == ConstraintType.CARD && isRoot && childId == 1) {
                        continue;
                    }

                    ArrayList<Long> childBaseIdSet = child.baseIdSet();
                    baseIdSet.addAll(childBaseIdSet);

                    ++childId;
                }
            }

            Collections.sort(baseIdSet);
        }

        return baseIdSet;
    }

    public ConstraintType constraintType()
    {
        return constraintType;
    }

    public JoinNode.DistributionType getDistributionType()
    {
        return joinDistType;
    }

    public void setDistributionType(JoinNode.DistributionType joinDistTypeParam)
    {
        joinDistType = joinDistTypeParam;
    }

    private void setPartitioning(ArrayList<JoinConstraintNode> partitioningParam)
    {
        if (partitioningParam != null) {
            partitioning = new ArrayList<String>();
            for (JoinConstraintNode column : partitioningParam) {
                partitioning.add(column.name);
            }
        }
        else {
            partitioning = null;
        }
    }

    public JoinConstraintNode(JoinNode joinNode, boolean... ignoreDistribution)
    {
        requireNonNull(joinNode, "join is null");
        id = null;
        children = null;
        joinConstraintString = null;
        idSet = new ArrayList<Long>();
        baseIdSet = null;
        sourceNode = joinNode;
        name = null;

        if ((ignoreDistribution.length == 0 || !ignoreDistribution[0]) && joinNode.getDistributionType().isPresent()) {
            setDistributionType(joinNode.getDistributionType().get());
        }
        else {
            setDistributionType(null);
        }

        isRoot = true;
        partitioning = null;
        constraintType = ConstraintType.JOIN;
    }

    public JoinConstraintNode(SemiJoinNode semiJoinNode, boolean... ignoreDistribution)
    {
        requireNonNull(semiJoinNode, "join is null");
        id = null;
        children = null;
        joinConstraintString = null;
        idSet = new ArrayList<Long>();
        baseIdSet = null;
        sourceNode = semiJoinNode;

        if (!(ignoreDistribution.length == 0 || !ignoreDistribution[0]) && semiJoinNode.getDistributionType().isPresent()) {
            if (semiJoinNode.getDistributionType().get() == SemiJoinNode.DistributionType.PARTITIONED) {
                setDistributionType(JoinNode.DistributionType.PARTITIONED);
            }
            else {
                setDistributionType(JoinNode.DistributionType.REPLICATED);
            }
        }
        else {
            setDistributionType(null);
        }

        isRoot = true;
        name = null;
        partitioning = null;
        constraintType = ConstraintType.JOIN;
    }

    public PlanNode getSourceNode()
    {
        return sourceNode;
    }

    public Long joinId()
    {
        return id;
    }

    public void setId(Long joinIdParam)
    {
        id = joinIdParam;
        idSet.add(id);
        Collections.sort(idSet);
    }

    public void setJoinIdsFromTableOrAliasName(HashMap<String, Integer> joinIdMap, Multimap<String, String> locationToTableOrAliasNameMap)
    {
        requireNonNull(joinIdMap, "join id map is null");
        requireNonNull(locationToTableOrAliasNameMap, "location-to-name map is null");
        if (this.id == null && name != null) {
            String lookUpString = null;

            List<String> values = locationToTableOrAliasNameMap.values().stream().filter(v -> v.equals(name)).collect(Collectors.toList());
            if (values.size() > 0) {
                Set<String> uniqueValues = locationToTableOrAliasNameMap.values().stream().filter(v -> v.equals(name)).collect(Collectors.toSet());
                if (uniqueValues.size() == values.size()) {
                    for (Map.Entry<String, String> entry : locationToTableOrAliasNameMap.entries()) {
                        if (entry.getValue().equals(name)) {
                            lookUpString = entry.getKey();
                            break;
                        }
                    }
                }
                else {
                    throw new PrestoException(GENERIC_INTERNAL_ERROR, format("table or alias %s is not unique", name));
                }
            }

            if (lookUpString == null) {
                throw new PrestoException(GENERIC_INTERNAL_ERROR, format("no lookup string for table %s", name));
            }

            Long joinId;
            Integer value = joinIdMap.get(lookUpString);

            if (value != null) {
                joinId = Long.valueOf(value);
            }
            else {
                throw new PrestoException(GENERIC_INTERNAL_ERROR, format("Join id not found : %s", name));
            }

            setId(joinId);
        }
        else if (children != null) {
            idSet.clear();
            int childId = 0;
            for (JoinConstraintNode child : children) {
                if (constraintType == ConstraintType.CARD && isRoot && childId == 1) {
                    continue;
                }

                child.setJoinIdsFromTableOrAliasName(joinIdMap, locationToTableOrAliasNameMap);
                idSet.addAll(child.idSet);
                Collections.sort(idSet);

                if (idSet.stream().distinct().count() != idSet.size()) {
                    throw new PrestoException(GENERIC_INTERNAL_ERROR, "Duplicate join id");
                }

                ++childId;
            }
        }
    }

    public boolean joinIsValid(ArrayList<JoinConstraintNode> joinConstraints, OptTrace optTrace)
    {
        if (optTrace != null) {
            String joinConstraintString = this.joinConstraintString();
            optTrace.begin("joinIsValid");
            optTrace.msg("Join : %s", true, joinConstraintString);
        }

        boolean valid;

        if (joinConstraints == null || joinConstraints.isEmpty()) {
            valid = true;
        }
        else {
            valid = false;
            boolean oneApplicable = false;

            for (JoinConstraintNode constraint : joinConstraints) {
                if (constraint.constraintType() == ConstraintType.JOIN) {
                    if (optTrace != null) {
                        optTrace.msg("Next join constraint : %s", true, constraint.joinConstraintString());
                    }
                    ConstraintCompare cmp = satisfies(constraint);
                    if (optTrace != null) {
                        optTrace.incrIndent(1);
                        optTrace.msg("Result : %s", true, cmp.getString());
                        optTrace.decrIndent(1);
                    }
                    if (cmp == ConstraintCompare.TRUE) {
                        valid = true;
                        break;
                    }
                    else if (cmp == ConstraintCompare.FALSE) {
                        oneApplicable = true;
                    }
                }
            }

            if (!valid && !oneApplicable) {
                valid = true;
            }
        }

        if (optTrace != null) {
            optTrace.msg("** JOIN VALID ? %s **", true, valid ? "TRUE" : "FALSE");
            optTrace.end("joinIsValid");
        }

        return valid;
    }

    public boolean satisfiesAnyConstraint(ArrayList<JoinConstraintNode> joinConstraints, boolean... ignoreDistributionType)
    {
        boolean satisfiesAny = false;
        if (joinConstraints != null && !joinConstraints.isEmpty()) {
            for (JoinConstraintNode constraint : joinConstraints) {
                JoinNode.DistributionType saveJoinDistType = constraint.getDistributionType();
                if (ignoreDistributionType.length > 0 && ignoreDistributionType[0]) {
                    constraint.setDistributionType(null);
                }

                ConstraintCompare cmp = satisfies(constraint);

                constraint.setDistributionType(saveJoinDistType);

                if (cmp == ConstraintCompare.TRUE) {
                    satisfiesAny = true;
                    break;
                }
            }
        }

        return satisfiesAny;
    }

    public Long cardinality(ArrayList<JoinConstraintNode> joinConstraints, OptTrace optTrace)
    {
        Long cardinality = null;
        if (joinConstraints != null && !joinConstraints.isEmpty()) {
            for (JoinConstraintNode constraint : joinConstraints) {
                if (constraint.constraintType() == ConstraintType.CARD) {
                    cardinality = matchCardinality(constraint);

                    if (cardinality != null) {
                        if (optTrace != null) {
                            optTrace.msg("Matched cardinality constraint : %s", true, constraint.joinConstraintString());
                        }
                        break;
                    }
                }
            }
        }

        return cardinality;
    }

    private JoinConstraintNode find(Long joinId, String tableOrAliasName, ArrayList<JoinConstraintNode> childMappings,
            JoinNode.DistributionType distType)
    {
        JoinConstraintNode foundJoinConstraintNode = null;
        requireNonNull(childMappings, "child mappings is null");

        boolean distTypeOk = true;
        if (distType != null) {
            if (this.joinDistType != null && !distType.equals(this.joinDistType)) {
                distTypeOk = false;
            }
        }
        else {
            if (this.joinDistType != null) {
                distTypeOk = false;
            }
        }

        if (distTypeOk) {
            if (joinId != null && this.id != null && joinId == this.id) {
                foundJoinConstraintNode = this;
            }
            else if (tableOrAliasName != null && this.name != null && tableOrAliasName == this.name) {
                foundJoinConstraintNode = this;
            }
            else if (childMappings.size() > 0) {
                boolean matchedChildren = false;
                if (this.children != null && this.children.size() == childMappings.size()) {
                    matchedChildren = true;
                    for (int i = 0; i < childMappings.size() && matchedChildren; ++i) {
                        matchedChildren = this.children.get(i).equals(childMappings.get(i));
                    }
                }

                if (matchedChildren) {
                    foundJoinConstraintNode = this;
                }
            }
        }

        for (int i = 0; foundJoinConstraintNode == null && this.children != null && i < this.children.size(); ++i) {
            foundJoinConstraintNode = this.children.get(i).find(joinId, tableOrAliasName, childMappings, distType);
        }

        return foundJoinConstraintNode;
    }

    private Long matchCardinality(JoinConstraintNode otherJoinConstraintNode)
    {
        Long card = null;
        requireNonNull(otherJoinConstraintNode, "unexpected null");
        if (otherJoinConstraintNode.constraintType == ConstraintType.CARD) {
            checkArgument(otherJoinConstraintNode.children.size() == 2, "expected 2 inputs");

            JoinConstraintNode left = otherJoinConstraintNode.children.get(0);

            if (this.baseIdSet().equals(left.baseIdSet())) {
                JoinConstraintNode right = otherJoinConstraintNode.children.get(1);
                checkArgument(right.id != null, "expected a number");
                card = right.id;
            }
        }

        return card;
    }

    private JoinConstraintNode matchJoin(JoinConstraintNode otherJoinConstraintNode)
    {
        JoinConstraintNode match = null;

        ArrayList<JoinConstraintNode> childMappings = new ArrayList<>();
        boolean allChildrenMatch = true;
        for (int i = 0; children != null && i < children.size() && match == null; ++i) {
            JoinConstraintNode matchedChild = children.get(i).matchJoin(otherJoinConstraintNode);
            if (matchedChild != null) {
                if (matchedChild == otherJoinConstraintNode) {
                    match = matchedChild;
                }
                else {
                    childMappings.add(matchedChild);
                }
            }
            else {
                allChildrenMatch = false;
            }
        }

        if (match == null && allChildrenMatch) {
            match = otherJoinConstraintNode.find(id, name, childMappings, joinDistType);
        }

        return match;
    }

    public ConstraintCompare satisfies(JoinConstraintNode otherJoinConstraintNode)
    {
        ConstraintCompare satisfiesConstraint;

        if (otherJoinConstraintNode != null) {
            if (this.constraintType == ConstraintType.JOIN && otherJoinConstraintNode.constraintType == ConstraintType.JOIN) {
                if (!joinIdsIntersect(otherJoinConstraintNode)) {
                    satisfiesConstraint = ConstraintCompare.NOT_APPLICABLE;
                }
                else if (matchJoin(otherJoinConstraintNode) != null) {
                    satisfiesConstraint = ConstraintCompare.TRUE;
                }
                else {
                    satisfiesConstraint = ConstraintCompare.FALSE;
                }
            }
            else {
                satisfiesConstraint = ConstraintCompare.NOT_APPLICABLE;
            }
        }
        else {
            satisfiesConstraint = ConstraintCompare.TRUE;
        }

        return satisfiesConstraint;
    }

    public boolean joinIdsIntersect(JoinConstraintNode otherJoinConstraintNode)
    {
        requireNonNull(otherJoinConstraintNode, "unexpected null join constraint node");
        boolean intersects = false;
        if (!idSet.isEmpty() && !otherJoinConstraintNode.idSet.isEmpty()) {
            for (Long joinId : idSet) {
                if (otherJoinConstraintNode.idSet.contains(joinId)) {
                    intersects = true;
                    break;
                }
            }
        }

        return intersects;
    }

    public void appendChild(JoinConstraintNode child)
    {
        if (children == null) {
            children = new ArrayList<>();
        }

        children.add(child);
        child.isRoot = false;
        ArrayList<Long> childjoinIdSet = child.idSet;
        for (Long childjoinId : childjoinIdSet) {
            if (idSet.contains(childjoinId)) {
                throw new PrestoException(GENERIC_INTERNAL_ERROR, format("duplicate join id : %d", childjoinId));
            }
        }
        idSet.addAll(childjoinIdSet);
        Collections.sort(idSet);
    }

    private String buildJoinConstraintString()
    {
        StringBuilder builder = new StringBuilder();
        if (isRoot == true && children != null && children.size() > 1) {
            builder.append(this.constraintType.getString());
        }

        if (children == null || children.size() == 0) {
            if (name != null) {
                builder.append(name);
            }
            else if (id != null) {
                builder.append(id);
            }
        }
        else {
            boolean first = true;
            builder.append("(");
            for (JoinConstraintNode child : children) {
                if (!first) {
                    builder.append(" ");
                }

                String childJoinConstraintString = child.joinConstraintString();

                int startPos = childJoinConstraintString.indexOf("JOIN", 0);

                if (startPos < 0) {
                    startPos = childJoinConstraintString.indexOf("CARD", 0);
                }

                if (startPos >= 0) {
                    childJoinConstraintString = childJoinConstraintString.substring(startPos + 4);
                }

                builder.append(childJoinConstraintString);
                first = false;
            }

            builder.append(")");
        }

        if (joinDistType != null) {
            switch (joinDistType) {
                case PARTITIONED:
                    builder.append(" [P]");
                    break;
                case REPLICATED:
                    builder.append(" [R]");
                    break;
                default:
                    builder.append(" [?]");
                    break;
            }
        }

        return builder.toString();
    }

    public String joinConstraintString()
    {
        if (joinConstraintString == null) {
            joinConstraintString = buildJoinConstraintString();
        }

        return joinConstraintString;
    }

    private static enum Token
    {LPAR, RPAR, NUMBER, NAME, EOF, SPACE, LBRACKET, RBRACKET, PARTITIONED, REPLICATED};

    private static class Scanner
    {
        private final Reader in;
        private int c;
        private Token token;
        private long number;
        private String name;

        public Scanner(Reader in)
                throws IOException
        {
            this.in = in;
            c = in.read();
        }

        public Token getToken()
        {
            return token;
        }

        public long getNumber()
        {
            return number;
        }

        public String getName()
        {
            return name;
        }

        public Token nextToken()
                throws IOException
        {
            while (c == ' ') {
                c = in.read();
            }

            if (c < 0) {
                token = Token.EOF;
                return token;
            }
            if (c >= '0' && c <= '9') {
                number = c - '0';
                c = in.read();
                while (c >= '0' && c <= '9') {
                    number = 10 * number + (c - '0');
                    c = in.read();
                }

                token = Token.NUMBER;
                return token;
            }

            switch (c) {
                case '(':
                    token = Token.LPAR;
                    break;
                case ')':
                    token = Token.RPAR;
                    break;
                case '[':
                    token = Token.LBRACKET;
                    break;
                case ']':
                    token = Token.RBRACKET;
                    break;
                case 'P':
                    token = Token.PARTITIONED;
                    break;
                case 'R':
                    token = Token.REPLICATED;
                    break;
                default:
                    StringBuilder builder = new StringBuilder();
                    while (c != ' ' && c != ')') {
                        builder.append((char) c);
                        c = in.read();
                    }
                    name = builder.toString();
                    if (!name.isEmpty()) {
                        token = Token.NAME;
                        return token;
                    }
            }

            c = in.read();
            return token;
        }
    }

    private static ArrayList<JoinConstraintNode> parseList(Scanner scanner, ConstraintType constraintType)
            throws IOException
    {
        ArrayList<JoinConstraintNode> nodes = new ArrayList<JoinConstraintNode>();
        if (scanner.getToken() != Token.RPAR) {
            nodes.add(parse(scanner, constraintType));

            while (scanner.getToken() != Token.RPAR) {
                if (scanner.getToken() == Token.EOF) {
                    throw new RuntimeException("expected EOF when parsing constraint string");
                }

                JoinConstraintNode newJoinConstraintNode = parse(scanner, constraintType);

                nodes.add(newJoinConstraintNode);
            }
        }

        return nodes;
    }

    public static void parse(String constraintString, ArrayList<JoinConstraintNode> joinConstraints)
            throws IOException
    {
        requireNonNull(constraintString, "constraint string is null");
        requireNonNull(joinConstraints, "constraint list is null");

        ConstraintType constraintType = ConstraintType.JOIN;

        constraintString = constraintString.trim();
        String upperCaseConstraintString = constraintString.toUpperCase();
        int startPos1 = upperCaseConstraintString.indexOf("JOIN", 0);
        int startPos2 = upperCaseConstraintString.indexOf("CARD", 0);

        int startPos;
        if (startPos2 == -1) {
            startPos = startPos1;
            constraintType = ConstraintType.JOIN;
        }
        else if (startPos1 == -1) {
            startPos = startPos2;
            constraintType = ConstraintType.CARD;
        }
        else if (startPos1 < startPos2) {
            startPos = startPos1;
            constraintType = ConstraintType.JOIN;
        }
        else {
            startPos = startPos2;
            constraintType = ConstraintType.CARD;
        }

        int endPos = constraintString.length();

        while (startPos >= 0 && startPos < endPos) {
            startPos += 4;
            String nextConstraintString = null;
            int nextPos1 = upperCaseConstraintString.indexOf("JOIN", startPos);
            int nextPos2 = upperCaseConstraintString.indexOf("CARD", startPos);

            int nextPos;
            ConstraintType nextConstraintType;

            if (nextPos2 == -1) {
                nextPos = nextPos1;
                nextConstraintType = ConstraintType.JOIN;
            }
            else if (nextPos1 == -1) {
                nextPos = nextPos2;
                nextConstraintType = ConstraintType.CARD;
            }
            else if (nextPos1 < nextPos2) {
                nextPos = nextPos1;
                nextConstraintType = ConstraintType.JOIN;
            }
            else {
                nextPos = nextPos2;
                nextConstraintType = ConstraintType.CARD;
            }

            if (nextPos > 0 && nextPos < endPos) {
                nextConstraintString = constraintString.substring(startPos, nextPos).trim();
            }
            else {
                nextConstraintString = constraintString.substring(startPos, endPos);
            }

            StringReader in = new StringReader(nextConstraintString);
            Scanner scanner = new Scanner(in);
            scanner.nextToken();
            JoinConstraintNode joinConstraintNode = null;

            try {
                joinConstraintNode = parse(scanner, constraintType);
            }
            catch (IOException e) {
                System.err.println("Invalid join constraint : " + nextConstraintString);
                joinConstraintNode = null;
            }

            if (joinConstraintNode != null) {
                joinConstraints.add(joinConstraintNode);
            }

            startPos = nextPos;
            constraintType = nextConstraintType;
        }

        return;
    }

    private static JoinConstraintNode parse(Scanner scanner, ConstraintType constraintType)
            throws IOException
    {
        switch (scanner.getToken()) {
            case NUMBER:
                long value = scanner.getNumber();
                scanner.nextToken();
                return new JoinConstraintNode((TableScanNode) null, value, null, constraintType);
            case NAME:
                String name = scanner.getName();
                scanner.nextToken();
                return new JoinConstraintNode((TableScanNode) null, null, name, constraintType);
            case LPAR:
                scanner.nextToken();
                ArrayList<JoinConstraintNode> nodes = parseList(scanner, constraintType);

                if (scanner.getToken() != Token.RPAR) {
                    throw new RuntimeException(") expected");
                }

                scanner.nextToken();

                JoinNode.DistributionType distType = null;
                ArrayList<JoinConstraintNode> partitioning = null;
                if (scanner.getToken() == Token.LBRACKET) {
                    scanner.nextToken();

                    if (scanner.getToken() == Token.PARTITIONED) {
                        distType = JoinNode.DistributionType.PARTITIONED;
                    }
                    else {
                        distType = JoinNode.DistributionType.REPLICATED;
                    }

                    scanner.nextToken();

                    if (scanner.getToken() == Token.LPAR) {
                        scanner.nextToken();
                        partitioning = parseList(scanner, constraintType);
                        scanner.nextToken();
                    }

                    if (scanner.getToken() != Token.RBRACKET) {
                        throw new RuntimeException("] expected");
                    }

                    scanner.nextToken();
                }

                JoinConstraintNode newNode = new JoinConstraintNode(nodes, constraintType);
                newNode.setDistributionType(distType);
                return newNode;
            case EOF:
                return null;
            default:
                throw new RuntimeException("Number or ( expected");
        }
    }
}
