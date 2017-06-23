package mcparser.instr;

import java.util.logging.Level;
import java.util.logging.Logger;
import mcparser.*;
import mcparser.util.*;

import java.util.*;
import java.io.*;
import javax.swing.JOptionPane;

import org.apache.bcel.Repository;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;

public class InstructionInfo
{

    public static boolean implementsInterface(ClassGen cgen, String interfaceName)
    {
        try
        {
            JavaClass[] interfaces = cgen.getJavaClass().getAllInterfaces();
            for (JavaClass jclass : interfaces)
            {
                if (jclass.getClassName().equals(interfaceName))
                    return true;
            }
        }
        catch (ClassNotFoundException ex) {}
        return false;
    }
    
    public static ClassGen getClassGen(String classname)
    {
        try
        {
            JavaClass jclass = Repository.lookupClass(classname);
            return new ClassGen(jclass);
        }
        catch (ClassNotFoundException ex)
        {
            return null;
        }
    }
    
    public static boolean containsMethod(ClassGen cgen, String methodSig)
    {
        for (Method m : cgen.getMethods())
        {
            if ((m.getName()+m.getSignature()).equals(methodSig))
                return true;
        }
        return false;
    }

    public static MethodGen getMethodFromClass(ClassGen cgen, String methodSig)
    {
        for (Method m : cgen.getMethods())
        {
            if ((m.getName()+m.getSignature()).equals(methodSig))
                return new MethodGen(m,cgen.getClassName(),cgen.getConstantPool());
        }
        return null;
    }

    public static int getInstrHash(ClassGen cgen, MethodGen mgen, InstructionHandle ih)
    {
        return (new InstructionHandleData(cgen,mgen,ih)).hashCode();
    }

    public static String getInstrName(InstructionHandle ih)
    {
        return ih.getInstruction().getName();
    }
    
    public static String getInstrType(InstructionHandle ih)
    {
        Instruction instr = ih.getInstruction();

        if (instr instanceof InvokeInstruction)
            return "invoke";
        else if (instr instanceof BranchInstruction)
            return "branch";
        else if (instr instanceof GETFIELD ||
                 instr instanceof GETSTATIC)
            return "get";
        else if (instr instanceof PUTFIELD ||
                 instr instanceof PUTSTATIC)
            return "put";
        else if (instr instanceof ReturnInstruction)
            return "return";
        else if (instr instanceof LocalVariableInstruction)
            return "local";
        else if (instr instanceof TypedInstruction)
            return "typed";
        else
            return "default";
    }

    public static boolean isNew(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof NEW);
    }

    public static boolean isInvoke(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof InvokeInstruction);
    }

    public static boolean isBranch(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof BranchInstruction);
    }

    public static boolean isGetField(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof GETFIELD ||
                ih.getInstruction() instanceof GETSTATIC);
    }

    public static boolean isPutField(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof PUTFIELD ||
                ih.getInstruction() instanceof PUTSTATIC);
    }

    public static boolean isArith(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof ArithmeticInstruction);
    }

    public static boolean isLocalVariableInstr(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof LocalVariableInstruction);
    }

    public static boolean isLoad(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof LoadInstruction);
    }

    public static boolean isStore(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof StoreInstruction);
    }

    public static boolean isReturn(InstructionHandle ih)
    {
        return (ih.getInstruction() instanceof ReturnInstruction);
    }

    public static ClassGen getClassFromType(Type type)
            throws ClassNotFoundException
    {
        JavaClass calledJavaClass =
                Repository.lookupClass(
                type.toString());
        return new ClassGen(calledJavaClass);
    }

    public static ObjectType[] getThrownExceptions(InstructionHandle ih)
    {
        Instruction instr = ih.getInstruction();
        if (!(instr instanceof ExceptionThrower))
            return new ObjectType[0];
        
        Class[] classes = ((ExceptionThrower)instr).getExceptions();
        ArrayList<ObjectType> oTypeList = new ArrayList<ObjectType>();
        for (int i = 0; i < classes.length; i++)
        {
            if (!classes[i].getCanonicalName().equals("java.lang.NoSuchFieldError") &&
                !classes[i].getCanonicalName().equals("java.lang.NoSuchMethodError"))
                oTypeList.add(new ObjectType(classes[i].getCanonicalName()));
        }
        ObjectType[] oTypeArray = new ObjectType[oTypeList.size()];
        for (int i = 0; i < oTypeList.size(); i++)
            oTypeArray[i] = oTypeList.get(i);
        return oTypeArray;
    }
    
    /**
     * Based upon the thrown exception and the handle of the instruction
     * that threw it, looks at the current method's exception table to see
     * if there is a handler for it. If the current method does not have
     * a handler, returns null.
     * @param mgen The current method gen.
     * @param currentIH The current instruction handle
     * @param thrownExceptionType The exception thrown by the instruction.
     * @return The instruction handle that begins the exception handler, or
     *         null if one is not found.
     */
    public static InstructionHandle getExceptionHandler(
            MethodGen mgen,
            InstructionHandle currentIH,
            ObjectType thrownExceptionType)
                throws ClassNotFoundException
    {
        CodeExceptionGen[] exceptions = mgen.getExceptionHandlers();
        int currentOffset = currentIH.getPosition();
        for (CodeExceptionGen exception : exceptions)
        {
            ObjectType exceptionType = exception.getCatchType();
            // Are we in range? Are we a matching exception type?
            if (currentOffset >= exception.getStartPC().getPosition() &&
                currentOffset <= exception.getEndPC().getPosition() &&
                (exceptionType == null ||
                 exceptionType.equals(thrownExceptionType) ||
                 thrownExceptionType.subclassOf(exceptionType)))
            {
                return exception.getHandlerPC();
            }
        }
        // Default case if we can't find a handler in this method
        return null;
    }

    public static InvokeData getInvokeData(
            ClassGen cgen,
            InstructionHandle ih)
                throws BadInstructionHandleException, ClassNotFoundException
    {
        if (!(ih.getInstruction() instanceof InvokeInstruction))
            throw new BadInstructionHandleException("Handle's instruction not of type InvokeInstruction.");
        InvokeInstruction instr = (InvokeInstruction)ih.getInstruction();

        ConstantPoolGen cpgen = cgen.getConstantPool();

        InvokeData invokeData = new InvokeData();

        invokeData.args = instr.getArgumentTypes(cpgen);
        invokeData.objType = instr.getReferenceType(cpgen);
        invokeData.methodName = instr.getMethodName(cpgen);
        invokeData.retType = instr.getReturnType(cpgen);
        invokeData.signature = instr.getSignature(cpgen);
        invokeData.opname = instr.getName();
        JavaClass calledJavaClass = null;
        try
        {
            calledJavaClass =
                    Repository.lookupClass(
                    invokeData.objType.toString());
        } catch (ClassNotFoundException ex) { return null; }

        MethodGen calledMethodGen = Misc.getMethodGen(
                calledJavaClass,
                invokeData.methodName + invokeData.signature);
        
        if (calledMethodGen==null)
            return null;

        invokeData.cgen = new ClassGen(Repository.lookupClass(calledMethodGen.getClassName()));
        invokeData.mgen = calledMethodGen;

        invokeData.exceptions = getThrownExceptions(calledMethodGen);
        invokeData.modifiers = calledMethodGen.getModifiers();

        return invokeData;
    }

    public static ObjectType[] getThrownExceptions(MethodGen mgen)
    {
        if (mgen.getMethod().getExceptionTable() != null)
        {
            String[] exceptionNames =
                    mgen.getMethod().getExceptionTable().getExceptionNames();
            ObjectType[] oTypes = new ObjectType[exceptionNames.length];
            for (int i = 0; i < exceptionNames.length; i++)
            {
                oTypes[i] = new ObjectType(exceptionNames[i]);
            }
            return oTypes;
        }
        return new ObjectType[0];
    }

    public static ArrayList<MethodGen> getClassMethodsNoConstructors(ClassGen cgen)
    {
        // Note that this does not currently explore superclasses
        Method[] methods = cgen.getMethods();
        ArrayList<MethodGen> mgenList = new ArrayList<MethodGen>();
        for (Method method : methods)
        {
            if (!method.getName().equals("<init>") &&
                !method.getName().equals("<clinit>"))
            {
                mgenList.add(new MethodGen(method,cgen.getClassName(),cgen.getConstantPool()));
            }
        }
        return mgenList;
    }

    public static FieldOpData getFieldOpData(
            ClassGen cgen,
            InstructionHandle ih)
                throws BadInstructionHandleException, ClassNotFoundException
    {
        if (!(ih.getInstruction() instanceof FieldInstruction))
            throw new BadInstructionHandleException("Handle's instruction not of type FieldInstruction.");
        FieldInstruction instr = (FieldInstruction)ih.getInstruction();

        ConstantPoolGen cpgen = cgen.getConstantPool();

        FieldOpData fieldData = new FieldOpData();

        fieldData.objType = instr.getReferenceType(cpgen);
        fieldData.fieldName = instr.getFieldName(cpgen);
        fieldData.fieldType = instr.getFieldType(cpgen);
        fieldData.signature = instr.getSignature(cpgen);
        fieldData.opname = instr.getName();

        JavaClass calledJavaClass =
                Repository.lookupClass(
                fieldData.objType.toString());

        Field calledField = Misc.getField(
                calledJavaClass,
                fieldData.fieldName + fieldData.signature);
        if (calledField == null)
            return null;

        fieldData.cgen = new ClassGen(calledJavaClass);
        fieldData.fgen = new FieldGen(calledField,fieldData.cgen.getConstantPool());

        fieldData.modifiers = calledField.getModifiers();

        return fieldData;
    }

    public static boolean isPrimitive(Type type)
    {
        return !type.getSignature().startsWith("L");
    }

    public static InstructionHandle getBranchTarget(
            InstructionHandle ih)
                throws BadInstructionHandleException
    {
        if (!(ih.getInstruction() instanceof BranchInstruction))
            throw new BadInstructionHandleException("Handle's instruction not of type BranchInstruction.");
        BranchInstruction instr = (BranchInstruction)ih.getInstruction();

        return instr.getTarget();
    }

    public static InstructionHandle[] getSwitchTargets(
            InstructionHandle ih)
                throws BadInstructionHandleException
    {
        if (!(ih.getInstruction() instanceof Select))
            throw new BadInstructionHandleException("Handle's instruction not of type Select.");
        Select instr = (Select)ih.getInstruction();

        return instr.getTargets();
    }

    public static Object getLDCConstant(
            ClassGen cgen,
            InstructionHandle ih)
                throws BadInstructionHandleException
    {
        if (!(ih.getInstruction() instanceof LDC))
            throw new BadInstructionHandleException("Handle's instruction not of type LDCInstruction.");
        LDC instr = (LDC)ih.getInstruction();

        return instr.getValue(cgen.getConstantPool());
    }

    public static Type getTypedParam(
            ClassGen cgen,
            InstructionHandle ih)
                throws BadInstructionHandleException
    {
        if (!(ih.getInstruction() instanceof TypedInstruction))
            throw new BadInstructionHandleException("Handle's instruction not of type TypedInstruction.");
        TypedInstruction instr = (TypedInstruction)ih.getInstruction();

        return instr.getType(cgen.getConstantPool());
    }

    public static int getLocalVariableIndex(InstructionHandle ih)
            throws BadInstructionHandleException
    {
        if (!(ih.getInstruction() instanceof LocalVariableInstruction))
            throw new BadInstructionHandleException("Handle's instruction not of type LocalVariableInstruction.");
        LocalVariableInstruction instr = (LocalVariableInstruction)ih.getInstruction();

        return instr.getIndex();
    }

//    public static void getInstanceSize(Type type)
//            throws ClassNotFoundException
//    {
//        JavaClass calledJavaClass =
//                Repository.lookupClass(
//                type.toString());
//        Field[] fieldArray = calledJavaClass.getFields();
//        for (int i = 0; i < fieldArray.length; i++)
//        {
//        }
//    }

}
