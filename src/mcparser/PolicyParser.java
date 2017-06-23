package mcparser;

import java.util.*;

import org.apache.bcel.generic.*;

import org.nfunk.jep.*;
import org.lsmp.djep.xjep.*;
import org.nfunk.jep.function.*;

import spox.policy.*;
import spox.policy.PolicyComponent.*;

public class PolicyParser
{

    public static Policy getPolicy(String filename)
            throws Exception
    {
        return new Policy(filename);
    }

    public static ArrayList<ArrayList<TransData>> getTransData(
            Policy policy,
            InstructionHandle ih,
            ClassGen cgen,
            MethodGen mgen)
                throws ParseException
    {
        ArrayList<ArrayList<TransData>> transList = new ArrayList<ArrayList<TransData>>();

        for (Forall forall : policy.getData().forall)
        {
            getPointcutTransDataFromForall(
                transList,
                new HashMap<String,Integer>(),
                new HashMap<String,Integer>(),
                forall,
                ih,
                cgen,
                mgen);
        }

        for (Edge edge : policy.getData().edge)
        {
            if (PointcutMatcher.matchInstructionToPointcut(ih, cgen, mgen, edge.label.pointcut))
            {
                ArrayList<TransData> edgeTransList = new ArrayList<TransData>();
                for (Nodes nodes : edge.nodes)
                {
                    TransData transData = new TransData();
                    transData.after = edge.after;
                    transData.fromExpression = nodes.from;
                    transData.toExpression = nodes.to;
                    transData.iterVarStart = new HashMap<String,Integer>();
                    transData.iterVarEnd = new HashMap<String,Integer>();
                    transData.stateName = nodes.state;
                    transData.fromTree = parseEquation(nodes.from.toString());
                    if (!nodes.to.isBadState())
                        transData.toTree = parseEquation(nodes.to.toString());
                    else
                        transData.toTree = null;
                    edgeTransList.add(transData);
                }
                transList.add(edgeTransList);
            }
        }

        return transList;
    }

    private static void getPointcutTransDataFromForall(
            ArrayList<ArrayList<TransData>> transList,
            HashMap<String,Integer> iterVarStart,
            HashMap<String,Integer> iterVarEnd,
            Forall forall,
            InstructionHandle ih,
            ClassGen cgen,
            MethodGen mgen)
                throws ParseException
    {
        iterVarStart.put(forall.var, forall.from);
        iterVarEnd.put(forall.var, forall.to);

        for (Forall innerForall : forall.forall)
            getPointcutTransDataFromForall(transList,iterVarStart,iterVarEnd,innerForall,ih,cgen,mgen);

        for (Edge edge : forall.edge)
        {
            if (PointcutMatcher.matchInstructionToPointcut(ih, cgen, mgen, edge.label.pointcut))
            {
                ArrayList<TransData> edgeTransList = new ArrayList<TransData>();
                for (Nodes nodes : edge.nodes)
                {
                    TransData transData = new TransData();
                    transData.after = edge.after;
                    transData.fromExpression = nodes.from;
                    transData.toExpression = nodes.to;
                    transData.iterVarStart = iterVarStart;
                    transData.iterVarEnd = iterVarEnd;
                    transData.stateName = nodes.state;
                    transData.fromTree = parseEquation(nodes.from.toString());
                    if (!nodes.to.isBadState())
                        transData.toTree = parseEquation(nodes.to.toString());
                    else
                        transData.toTree = null;
                    edgeTransList.add(transData);
                }
                transList.add(edgeTransList);
            }
        }

    }

    public static Node getTopParentEquationNode(Node node)
    {
        if (node.jjtGetParent() != null)
            return getTopParentEquationNode(node.jjtGetParent());
        else
            return node;
    }
    
    public static Node parseEquation(String expression)
            throws ParseException
    {

        JEP jep = new JEP();
        jep.setAllowUndeclared(true);
        jep.parseExpression(expression);

        // Uncomment the following code to get console output
//        TreeUtils treeUtils = new TreeUtils();
//        Node[] nodeArray = treeUtils.getChildrenAsArray(jep.getTopNode());
//        System.out.println(treeUtils.getOperator(nodeArray[0].jjtGetParent()).getName());
//        for (int i = 0; i < nodeArray.length; i++)
//        {
//            if (treeUtils.isVariable(nodeArray[i]))
//                System.out.println(treeUtils.getName(nodeArray[i]));
//            else if (treeUtils.isOperator(nodeArray[i]))
//                System.out.println(treeUtils.getOperator(nodeArray[i]).toString());
//            else if (treeUtils.isInteger(nodeArray[i]))
//                System.out.println(treeUtils.getValue(nodeArray[i]));
//        }


        if (jep.getErrorInfo() != null)
            throw new ParseException("Expression '" + expression +
                    "' could not be parsed:\n" + jep.getErrorInfo());

        return jep.getTopNode();
    }

    public static String getNodeType(Node node)
    {;
        if (node instanceof ASTConstant)
            return "constant";
        if (node instanceof ASTFunNode)
            return "fun";
        if (node instanceof ASTVarNode)
            return "var";
        if (node instanceof ASTStart)
            return "start";
        return "default";
    }

}
