/*
 * Data structure containing all parameters needed by a pointcut checker
 * when seeing if a given policy input (commands, context, etc.)
 * matches a given pointcut.
 */

package mcparser;

import java.util.*;
import java.util.regex.*;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;
import org.apache.bcel.Repository;
import org.apache.bcel.util.*;
import org.apache.bcel.Constants;

import spox.policy.pointcut.PointcutComponent.*;
import spox.policy.pointcut.*;
import spox.policy.*;

/**
 * Written by Micah Jones
 */
public class PointcutData
{
    public Integer modifiers = null;
    public Type classType = null;
    public String memberName = null;
    public Type retType = null;
    public Type[] argType = null;
    public Type[] throwsType = null;
    
    public ClassGen cgen = null;
    public ConstantPoolGen cpgen = null;
    public Method method = null;
    public MethodGen mgen = null;
    public Instruction instruction = null;
    public InstructionHandle ih = null;

    //public ArrayList<

    /**
     * A list of all classes that have instance states attached.
     */
    public ArrayList<String> stateObj = new ArrayList<String>();
    /**
     * A mapping from an edge's instance variable id (e.g., 'obj="x"') to the
     * actual, fully qualified name of the object (e.g., java.lang.Object).
     */
    public HashMap<String, String> nodeObj = new HashMap<String, String>();
    public HashMap<String, Integer> nodeObjIndex = new HashMap<String, Integer>();
    
    /**
     * Tells the rewriter that an instance id variable is tied to the 'this' pointer.
     */
    public HashMap<String, Boolean> thisObj = new HashMap<String, Boolean>();    
}
