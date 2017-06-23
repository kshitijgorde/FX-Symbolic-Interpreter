package mcparser.instr;

import mcparser.*;
import mcparser.util.*;

import java.util.*;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;

public class InvokeData
{

    public Type[] args = null;
    public ReferenceType objType = null;
    public String methodName = null;
    public Type retType = null;
    public String signature = null;
    public ObjectType[] exceptions = null;
    public int modifiers = 0;
    public String opname = null;
    public ClassGen cgen = null;
    public MethodGen mgen = null;
    
}
