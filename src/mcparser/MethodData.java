package mcparser;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;

public class MethodData
{

    public InstructionHandle[] instructions;
    public String name;
    public Type[] args;
    public String[] exceptions;
    public Type returnType;
    public LocalVariableGen[] localVariables;

}
