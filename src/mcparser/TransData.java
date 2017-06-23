package mcparser;

import java.util.*;

import spox.policy.*;
import spox.policy.pointcut.PointcutComponent.*;

import org.nfunk.jep.*;

public class TransData
{
    public String stateName;
    public StateExpression fromExpression;
    public StateExpression toExpression;
    public Node fromTree;
    public Node toTree;
    public HashMap<String,Integer> iterVarStart;
    public HashMap<String,Integer> iterVarEnd;
    public boolean after;
}
