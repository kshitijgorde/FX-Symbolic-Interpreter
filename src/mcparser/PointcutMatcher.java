package mcparser;

import mcparser.util.*;

import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.*;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;
import org.apache.bcel.Repository;
import org.apache.bcel.util.*;
import org.apache.bcel.Constants;

import com.karneim.util.collection.regex.Pattern;

import spox.policy.*;
import spox.policy.PolicyComponent.*;
import spox.policy.pointcut.*;
import spox.policy.pointcut.PointcutComponent.*;

public class PointcutMatcher
{

    public static Edge[] matchExecution(
            Policy policy,
            ClassGen cgen,
            MethodGen mgen)
    {
        ArrayList<Edge> matchedEdgeArray = new ArrayList<Edge>();
        ArrayList<Edge> policyEdgeArray = policy.getData().edge;

        ConstantPoolGen cpgen = cgen.getConstantPool();
        Method method = mgen.getMethod();

        PointcutData pData = new PointcutData();
        pData.cgen = cgen;
        pData.cpgen = cgen.getConstantPool();
        pData.mgen = mgen;
        pData.method = method;
        pData.cpgen = cgen.getConstantPool();
        pData.classType =
                Type.getType("L" + cgen.getClassName().replace('.','/') + ";");
        pData.memberName = method.getName();
        pData.modifiers = method.getModifiers();
        pData.argType = method.getArgumentTypes();
        pData.retType = method.getReturnType();

        for (Edge edge : policyEdgeArray)
        {
            // Set up the variable-to-object name mapping
            for (int i = 0; i < edge.nodes.size(); i++)
            {
                if (!edge.nodes.get(i).objName.isEmpty())
                {
                    pData.nodeObj.put(edge.nodes.get(i).objName,
                            Policy.getStateObject(
                                edge.nodes.get(i), policy.getData().state));
                }
            }
            // Store all the state objects for pointcut reference
            for (int i = 0; i < policy.getData().state.size(); i++)
                pData.stateObj.add(policy.getData().state.get(i).objName);

            // Now match against the edge's pointcuts
            if (matchesPointcut(edge.label.pointcut,pData))
                matchedEdgeArray.add(edge);
        }

        Edge[] returnEdges = new Edge[matchedEdgeArray.size()];
        matchedEdgeArray.toArray(returnEdges);

        return returnEdges;
    }

    public static boolean matchInstructionToPointcut(
            InstructionHandle ih,
            ClassGen cgen,
            MethodGen mgen,
            Pointcut p)
    {
        PointcutData pData = new PointcutData();
        pData.ih = ih;
        pData.cgen = cgen;
        pData.mgen = mgen;
        return matchInstructionToPointcut(p,pData);
    }

    public static boolean matchInstructionToPointcut(
            Pointcut p,
            PointcutData pData)
    {
        Instruction instr = pData.ih.getInstruction();
        ConstantPoolGen cpgen = pData.cgen.getConstantPool();
        if (instr instanceof InvokeInstruction)
        {
            // Invokes
            InvokeInstruction invokeInstruction = (InvokeInstruction)instr;
            pData.instruction = instr;
            pData.method = pData.mgen.getMethod();
            pData.cpgen = cpgen;
            pData.classType =
                    invokeInstruction.
                    getReferenceType(cpgen);
            pData.memberName =
                    invokeInstruction.
                    getMethodName(cpgen).toString();
            pData.argType = invokeInstruction.
                    getArgumentTypes(cpgen);
            pData.retType =
                    invokeInstruction.
                    getReturnType(cpgen);
            if (Misc.classExists(invokeInstruction.getReferenceType(cpgen).toString()))
            {
                Method calledMethod = null;
                try
                {
                    calledMethod = Misc.getMethodGen(Repository.lookupClass(
                            invokeInstruction.getReferenceType(cpgen).toString()),
                            invokeInstruction.getMethodName(cpgen) + invokeInstruction.getSignature(cpgen)).getMethod();
                }
                catch (ClassNotFoundException ex) { }
                if (calledMethod != null)
                {
                    pData.modifiers = calledMethod.getModifiers();
                    if (calledMethod.getExceptionTable() != null)
                        pData.throwsType = Misc.constructType(calledMethod.getExceptionTable().getExceptionNames());
                }
            }
        }

        else if (instr instanceof FieldInstruction)
        {
            // Field ops
            FieldInstruction fieldInstruction = (FieldInstruction)instr;
            pData.instruction = instr;
            pData.method = pData.mgen.getMethod();
            pData.cpgen = cpgen;
            pData.classType =
                    fieldInstruction.
                    getReferenceType(cpgen);
            pData.memberName =
                    fieldInstruction.
                    getFieldName(cpgen).toString();
            pData.retType =
                    fieldInstruction.getFieldType(cpgen);
            if (Misc.classExists(pData.classType.toString()))
            {
                Field calledField = null;
                try
                {
                    calledField = Misc.getField(Repository.lookupClass(
                        fieldInstruction.getReferenceType(cpgen).toString()),
                        fieldInstruction.getFieldName(cpgen) + fieldInstruction.getSignature(cpgen));
                }
                catch (ClassNotFoundException ex) { }
                if (calledField != null)
                    pData.modifiers = calledField.getModifiers();
            }

        }

        else
        {
            // All other instructions
            pData.instruction = instr;
            pData.method = pData.mgen.getMethod();
            pData.cpgen = cpgen;

        }

        return matchesPointcut(p, pData);
    }

    /**
     * Matches an instruction against pointcuts in the policy.
     * Note that this method currently only handles statically decidable
     * pointcuts.
     * @param instr The instruction to match.
     * @param policy The policy to consult.
     * @param cgen The containing ClassGen.
     * @param mgen The containing MethodGen.
     * @return If an instruction was matched against the pointcut of
     *         at least one edge, an array consisting of all matched edges.
     *         If no edges were matched, null is returned.
     */
    public static Edge[] matchInstructionToEdges(
            InstructionHandle ih,
            Policy policy,
            ClassGen cgen,
            MethodGen mgen)
    {
        ArrayList<Edge> matchedEdgeArray = new ArrayList<Edge>();
        ArrayList<Edge> policyEdgeArray = policy.getData().edge;

        PointcutData pData = new PointcutData();

        for (Edge edge : policyEdgeArray)
        {
            // Set up the variable-to-object name mapping
            for (int i = 0; i < edge.nodes.size(); i++)
            {
                if (!edge.nodes.get(i).objName.isEmpty())
                {
                    pData.nodeObj.put(edge.nodes.get(i).objName,
                            Policy.getStateObject(
                                edge.nodes.get(i), policy.getData().state));
                }
            }
            // Store all the state objects for pointcut reference
            for (int i = 0; i < policy.getData().state.size(); i++)
                pData.stateObj.add(policy.getData().state.get(i).objName);

            // Now match against the edge's pointcuts
            if (matchInstructionToPointcut(edge.label.pointcut,pData))
                matchedEdgeArray.add(edge);
        }

        Edge[] returnEdges = new Edge[matchedEdgeArray.size()];
        matchedEdgeArray.toArray(returnEdges);

        return returnEdges;
    }

    // Utility methods for checking against specific patterns
    private static boolean matchesPointcut(
            Pointcut pointcut,
            PointcutData pData)
    {

        if (pointcut == null)
            return false;

        // See what we're working with
        if (pointcut instanceof Call)
            return matchesCall((Call)pointcut, pData);
        else if (pointcut instanceof Execution)
            return matchesExecution((Execution)pointcut, pData);
        else if (pointcut instanceof FieldOp)
            return matchesFieldOp((FieldOp)pointcut, pData);
        else if (pointcut instanceof Preinitialization)
            return matchesPreinitialization((Preinitialization)pointcut, pData);
        else if (pointcut instanceof Initialization)
            return matchesInitialization((Initialization)pointcut, pData);
        else if (pointcut instanceof StaticInitialization)
            return matchesStaticInitialization((StaticInitialization)pointcut, pData);
        else if (pointcut instanceof Handler)
            return matchesHandler((Handler)pointcut, pData);
        else if (pointcut instanceof Instr)
            return matchesInstr((Instr)pointcut, pData);
        else if (pointcut instanceof ArgVal)
            return matchesArgVal((ArgVal)pointcut, pData);
        else if (pointcut instanceof ArgTyp)
            return matchesArgTyp((ArgTyp)pointcut, pData);
        else if (pointcut instanceof This)
            return matchesThis((This)pointcut, pData);
        else if (pointcut instanceof Target)
            return matchesTarget((Target)pointcut, pData);
        else if (pointcut instanceof Within)
            return matchesWithin((Within)pointcut, pData);
        else if (pointcut instanceof WithinCode)
            return matchesWithinCode((WithinCode)pointcut, pData);
        else if (pointcut instanceof BooleanOp)
            return matchesBooleanOp((BooleanOp)pointcut, pData);
        else if (pointcut instanceof After)
            return matchesAfter((After)pointcut, pData);
        else if (pointcut instanceof True)
            return true;
        else if (pointcut instanceof False)
            return false;
        else if (pointcut instanceof DynamicTrue)
            return true;
        else if (pointcut instanceof PointcutId)
            return matchesPointcut(Policy.getPointcutDef(((PointcutId)pointcut).name), pData);

        // If nothing above matched, return false
        return false;

    }

    private static boolean matchesCall(
            Call call,
            PointcutData pData)
    {
        // See if the data matches the execution pointcut
        // A nuance: If the class name is excluded from the pointcut,
        // we match up with calls to methods within this class.

        // Confirm that this was indeed a call instruction
        if (pData.instruction == null)
            return false;
        if (!(pData.instruction instanceof InvokeInstruction))
            return false;

        boolean isCP = true; // Tracks if this is *just* constructor patterns
        boolean hasClassName = false; // Tracks whether a class name is specified
        boolean retVal = true;

        // Check against each component; as soon as we hit something that
        // returns 'false', we jump out and return that
        // A 'true' returns only if EVERYTHING clears
        for (int i = 0; (i < call.mp.size() && retVal); i++)
        {
            MemberPattern mp = call.mp.get(i);
            if (mp instanceof Modifier)
                retVal = matchesModifier((Modifier)mp, pData.modifiers);
            else if (mp instanceof ClassId)
            {
                retVal = matchesClassId((ClassId)mp, pData.classType);
                hasClassName = true;
            }
            else if (mp instanceof MemberId)
            {
                if (!((MemberId)mp).mname.text.equalsIgnoreCase("new"))
                {
                    retVal = matchesMemberId((MemberId)mp, pData.memberName);
                    isCP = false;
                }
            }
            else if (mp instanceof RetType)
            {
                retVal = matchesRetType((RetType)mp, pData.retType);
                isCP = false;
            }
        }

        if (!hasClassName)
            retVal = retVal && (pData.classType.toString().equals(pData.cgen.getClassName()));

        // If we didn't have a member name or return type, we were given a
        // sequence of constructor patterns, and so we return true ONLY
        // if the method name given was <init>
        if (isCP && retVal)
            retVal = (pData.memberName.equals("<init>"));

        return retVal;

    }

    private static boolean matchesExecution(
            Execution execution,
            PointcutData pData)
    {
        // See if the data matches the execution pointcut

        // If we were given an instruction AT ALL, this doesn't match
        // (Executions are not matched on instructions)
        if (pData.instruction != null)
            return false;

        boolean isCP = true; // Tracks if this is *just* constructor patterns
        boolean retVal = true;

        // Check against each component; as soon as we hit something that
        // returns 'false', we jump out and return that
        // A 'true' returns only if EVERYTHING clears
        for (int i = 0; (i < execution.mp.size() && retVal); i++)
        {
            MemberPattern mp = execution.mp.get(i);
            if (mp instanceof Modifier)
                retVal = matchesModifier((Modifier)mp, pData.modifiers);
            else if (mp instanceof ClassId)
                retVal = matchesClassId((ClassId)mp, pData.classType);
            else if (mp instanceof MemberId)
            {
                if (!((MemberId)mp).mname.text.equalsIgnoreCase("new"))
                {
                    retVal = matchesMemberId((MemberId)mp, pData.memberName);
                    isCP = false;
                }
            }
            else if (mp instanceof RetType)
            {
                retVal = matchesRetType((RetType)mp, pData.retType);
                isCP = false;
            }
        }

        // If we didn't have a member name or return type, we were given a
        // sequence of constructor patterns, and so we return true ONLY
        // if the method name given was <init>
        if (isCP && retVal)
            retVal = (pData.memberName.equals("<init>"));

        return retVal;

    }

    private static boolean matchesPreinitialization(
            Preinitialization preinitialization,
            PointcutData pData)
    {
        // See if the data matches the preinitialization pointcut
        // Note that this is just a simplified version of execution

        // If we were given an instruction AT ALL, this doesn't match
        // (Executions are not matched on instructions)
        if (pData.instruction != null)
            return false;

        boolean retVal = (pData.memberName.equals("<init>"));

        // Check against each component; as soon as we hit something that
        // returns 'false', we jump out and return that
        // A 'true' returns only if EVERYTHING clears
        for (int i = 0; (i < preinitialization.mp.size() && retVal); i++)
        {
            MemberPattern mp = preinitialization.mp.get(i);
            if (mp instanceof Modifier)
                retVal = matchesModifier((Modifier)mp, pData.modifiers);
            else if (mp instanceof ClassId)
                retVal = matchesClassId((ClassId)mp, pData.classType);
        }

        return retVal;

    }

    private static boolean matchesInitialization(
            Initialization initialization,
            PointcutData pData)
    {
        // See if the data matches the initialization pointcut
        // Note that this is similar to an execution, but for a specific
        // section of code (specifically, that which immediately follows
        // the superclass's constructor call)

        // If we were given not given an instruction, we can't do anything
        if (pData.instruction == null)
            return false;

        boolean retVal = (pData.memberName.equals("<init>"));

        // Check against each component; as soon as we hit something that
        // returns 'false', we jump out with that
        // A 'true' occurs only if EVERYTHING clears
        for (int i = 0; (i < initialization.mp.size() && retVal); i++)
        {
            MemberPattern mp = initialization.mp.get(i);
            if (mp instanceof Modifier)
                retVal = matchesModifier((Modifier)mp, pData.modifiers);
            else if (mp instanceof ClassId)
                retVal = matchesClassId((ClassId)mp, pData.classType);
        }

        // If we're in the right method, let's now see if we're at a point
        // immediately succeeding a constructor call
        if (retVal)
        {
            if (pData.ih.getPrev() == null)
                return false;
            Instruction prevInstruction = pData.ih.getPrev().getInstruction();
            if (prevInstruction instanceof InvokeInstruction)
            {
                InvokeInstruction invoke = (InvokeInstruction)prevInstruction;
                retVal = retVal &&
                        (invoke.getMethodName(pData.cpgen).equals("<init>") &&
                        invoke.getReferenceType(pData.cpgen).toString().
                            equals(pData.cgen.getSuperclassName()));
                // TODO: Handle multiple constructors for that class...
                // (Probably have to use dynamics)
            }
            else
                return false;
        }

        return retVal;

    }

    private static boolean matchesStaticInitialization(
            StaticInitialization staticInitialization,
            PointcutData pData)
    {
        // See if the data matches the staticInitialization pointcut
        // Note that this is just a simplified version of execution

        // If we were given an instruction AT ALL, this doesn't match
        // (Executions are not matched on instructions)
        if (pData.instruction != null)
            return false;

        boolean retVal = (pData.memberName.equals("<clinit>")) &&
                matchesTypeName(staticInitialization.tname, pData.cgen.getClassName());

        return retVal;

    }

    private static boolean matchesHandler(
            Handler handler,
            PointcutData pData)
    {
        // See if the data matches the handler pointcut
        // This is similar to an execution, but instruction-based

        // We can't do anything if we aren't given an instruction to check
        if (pData.instruction == null)
            return false;

        CodeExceptionGen[] exHandler = pData.mgen.getExceptionHandlers();
        for (int i = 0; i < exHandler.length; i++)
        {
            if (exHandler[i].getHandlerPC().equals(pData.ih) &&
                    matchesTypeName(handler.tname, exHandler[i].getCatchType().toString()))
                return true;
        }

        return false;

    }

    private static boolean matchesFieldOp(
            FieldOp fieldOp,
            PointcutData pData)
    {
        // See if the data matches the field op

        // We need an instruction to tell us whether it's a get or set
        if (pData.instruction == null)
            return false;
        // Make sure it IS a field op
        if (!(pData.instruction instanceof FieldInstruction))
            return false;

        // Make sure that we can look at a get or set(put)
        if (pData.instruction.getName().startsWith("get"))
        {
            if (!(fieldOp instanceof GetField))
                return false;
        }
        else
        {
            if (!(fieldOp instanceof SetField))
                return false;
        }

        boolean hasClassName = false; // Tracks whether a class name is specified

        // Now that we know we match up with the specific instruction,
        // compare the field components
        boolean retVal = true;
        for (int i = 0; (i < fieldOp.mp.size() && retVal); i++)
        {
            MemberPattern mp = fieldOp.mp.get(i);
            if (mp instanceof Modifier)
                retVal = matchesModifier((Modifier)mp, pData.modifiers);
            else if (mp instanceof ClassId)
            {
                retVal = matchesClassId((ClassId)mp, pData.classType);
                hasClassName = true;
            }
            else if (mp instanceof MemberId)
                retVal = matchesMemberId((MemberId)mp, pData.memberName);
            else if (mp instanceof RetType)
                retVal = matchesRetType((RetType)mp, pData.retType);
        }

        if (!hasClassName)
            retVal = retVal && (pData.classType.toString().equals(pData.cgen.getClassName()));

        return retVal;

    }

    private static boolean matchesInstr(
            Instr instr,
            PointcutData pData)
    {
        // If no instruction data was given, we can't go on
        if (pData.instruction == null)
            return false;

        // See if the name matches
        return (matchesInstrName(instr.iname, pData.instruction.getName()));

    }

    private static boolean matchesArgVal(
            ArgVal argVal,
            PointcutData pData)
    {
        // An argVal checks the contents of the runtime stack, and is thus
        // a dynamic check. Based on the given instruction, an array of data
        // types is produced. If a given argument's type is not valid for
        // the requested comparison, this method returns false.
        // If it is, the contents of the instruction list at pData.returnIlist
        // is modified to contain a sequence of dynamic check instructions
        // to be inserted.

        // Locals
        Type[] type = new Type[0];

        // Figure out which kind of instruction this is
        if (pData.instruction == null) // Must be an execution check; get the method's args
            type = pData.argType;
        else if (pData.instruction instanceof InvokeInstruction)
            type = ((InvokeInstruction)pData.instruction).
                    getArgumentTypes(pData.cpgen);
        else if (pData.instruction instanceof FieldInstruction &&
                 pData.instruction.getName().startsWith("put"))
            type = new Type[] {((FieldInstruction)pData.instruction).
                    getFieldType(pData.cpgen)};
        else if (pData.instruction instanceof ReturnInstruction &&
                 pData.instruction.getOpcode() != Constants.RETURN)
            type = new Type[] {pData.mgen.getReturnType()};
        else
            return false;

        // Make sure we're within reasonable bounds (note that index 0
        // refers to the 'this' pointer when present, and should be referred
        // to with a <target> pointcut)
        if (argVal.num < 1 || argVal.num > type.length)
            return false;

        // Is this an instance item?
        if (pData.nodeObj.get(argVal.objName.text) != null)
        {
            ArrayList<String> superclassList = new ArrayList<String>();
            superclassList.add(type[argVal.num-1].toString());
            try
            {
                JavaClass[] superclass =
                        Repository.lookupClass(type[argVal.num-1].toString()).getSuperClasses();
                for (int i = 0; i < superclass.length; i++)
                {
                    if (pData.stateObj.contains(superclass[i].getClassName()))
                        superclassList.add(superclass[i].getClassName());
                }
            }
            catch (ClassNotFoundException ex)
            { /* Ignored for now */ }
            if (argVal.valExpr instanceof TrueExpr &&
                    superclassList.contains(pData.nodeObj.get(argVal.objName.text)))
            {
                System.out.println("Found " + argVal.objName.text + " at pos. " + (argVal.num));
                pData.nodeObjIndex.put(argVal.objName.text, new Integer(argVal.num));
                return true;
            }
            else
                return false;
        }

        // Make sure that we can check here (Note that '0' is a reserved
        // index for 'this' pointers regardless of whether one actually
        // exists for the given instruction)
//        if (argVal.valExpr instanceof TrueExpr)
//            return true;
        if (!(type[argVal.num-1].equals(Type.INT) || type[argVal.num-1].equals(Type.BOOLEAN)) &&
                argVal.valExpr instanceof IntCmp)
            return false;
        if (!(type[argVal.num-1] instanceof ObjectType) &&
                argVal.valExpr instanceof StrEq)
            return false;

        // Code generation; not desired for static analysis
        // TODO: Insert analysis of stack checks
//        if (pData.generateCode)
//            DynamicCodeBuilder.buildArgValCheck(argVal, pData, iBlock, type);

        return true;
    }

    private static boolean matchesArgTyp(
            ArgTyp argTyp,
            PointcutData pData)
    {
        // If we're working with a method definition (for a call or execution),
        // an ArgTyp checks the type of a parameter at some index i in the
        // parameter definition. If we are not given the data necessary
        // (which would be the case if we're not looking at a call or execution)
        // then this will always return false
        // For field accesses, the first arg is the field type

        // Locals
        Type[] type;

        // Figure out which kind of instruction this is
        if (pData.instruction == null) // Must be an execution check; get the method's args
            type = pData.method.getArgumentTypes();
        else if (pData.instruction instanceof InvokeInstruction)
            type = ((InvokeInstruction)pData.instruction).
                    getArgumentTypes(pData.cpgen);
        else if (pData.instruction instanceof FieldInstruction)
            type = new Type[] {((FieldInstruction)pData.instruction).
                    getFieldType(pData.cpgen)};
        else
            return false;

        // Make sure that we can check here (Note that '0' is a reserved
        // index for 'this' pointers regardless of whether one actually
        // exists for the given instruction (THIS IS NOT USABLE FOR ARGTYP))
        if (argTyp.num > type.length && argTyp.tname.text.isEmpty())
            return true; // A kludge; an empty typename lets us check argument list lengths
        if (argTyp.num < 1 || argTyp.num > type.length)
            return false;

        return matchesTypeName(argTyp.tname, type[argTyp.num-1].toString());

    }

    private static boolean matchesThis(
            This thisComponent,
            PointcutData pData)
    {
        // A This checks the type of the currently executing object (i.e., this)
        // Note that static methods will cause this to return false
        // (For universal checking of containing class's type, use Within)

        // Locals
        Type type;

        if (pData.mgen.isStatic())
            return false;

        // We know the method is virtual, so the type is in fact the class name

        // First check to see if this is an instance item
        type = Misc.constructType(pData.cgen.getClassName());
        if (pData.nodeObj.get(thisComponent.objName.text) != null)
        {
            ArrayList<String> superclassList = new ArrayList<String>();
            superclassList.add(type.toString());
            try
            {
                JavaClass[] superclass =
                        Repository.lookupClass(type.toString()).getSuperClasses();
                for (int i = 0; i < superclass.length; i++)
                {
                    if (pData.stateObj.contains(superclass[i].getClassName()))
                        superclassList.add(superclass[i].getClassName());
                }
            }
            catch (ClassNotFoundException ex)
            { /* Ignored for now */ }
            if (superclassList.contains(pData.nodeObj.get(thisComponent.objName.text)))
            {
                System.out.println("Found " + thisComponent.objName.text + " as this");
                pData.thisObj.put(thisComponent.objName.text, true);
                return true;
            }
            else
                return false;
        }

        // If we have a direct type match OR a match to any superclass or
        // interface or any interface's superclass,
        return matchesTypeAncestor(thisComponent.typeName, type.toString());

    }

    /**
     * If the value of type is a subclass or implementation of ancestorType,
     * returns true; false otherwise.
     * @param ancestorType The superclass or interface to compare with.
     * @param type The type to be checked.
     * @return True if compatible, false otherwise.
     */
    private static boolean matchesTypeAncestor(String ancestorType, String type)
    {
        ArrayList<String> ancestorList = new ArrayList<String>();
        ancestorList.add(type);
        try
        {
            JavaClass typeClass = Repository.lookupClass(type.toString());
            JavaClass[] superclass =
                    typeClass.getSuperClasses();
            for (int i = 0; i < superclass.length; i++)
                ancestorList.add(superclass[i].getClassName());
            JavaClass[] interfaceArray = typeClass.getAllInterfaces();
            for (int i = 0; i < interfaceArray.length; i++)
                ancestorList.add(interfaceArray[i].getClassName());
            return ancestorList.contains(ancestorType);
        }
        catch (ClassNotFoundException ex)
        { return false; }
    }

    private static boolean matchesTarget(
            Target target,
            PointcutData pData)
    {
        // If we're working with a method definition (for a call only),
        // a Target checks the type of the called class according to the
        // parameter definition. If we are not given the data necessary
        // (which would be the case if we're not looking at a call)
        // then this will always return false
        // For field accesses, we just get the type of the field
        // Note that for either case, static methods/fields will return false
        // for instance states and anything that would require an instanceof check

        // Locals
        Type type;
        Type[] argType = new Type[0];

        // Figure out which kind of instruction this is
        if (pData.instruction == null) // Must be an execution check; return false
            return false;
        else if (pData.instruction instanceof InvokeInstruction)
        {
            // If this is a static call and we're looking for specific
            // instance states, return false
            if (pData.instruction.getOpcode() == Constants.INVOKESTATIC &&
                    !target.objName.text.isEmpty())
                return false;
            // Otherwise, grab the type
            InvokeInstruction invoke = (InvokeInstruction)pData.instruction;
            type = invoke.getReferenceType(pData.cpgen);
            argType = new Type[invoke.getArgumentTypes(pData.cpgen).length+1];
            argType[0] = type;
            for (int i = 1; i < argType.length; i++)
                argType[i] = invoke.getArgumentTypes(pData.cpgen)[i-1];
        }
        else if (pData.instruction instanceof FieldInstruction)
        {
            if (pData.instruction.getName().endsWith("static") &&
                    !target.objName.text.isEmpty())
                return false;
            FieldInstruction field = (FieldInstruction)pData.instruction;
            type = field.getReferenceType(pData.cpgen);
            if (field.getName().startsWith("put"))
                argType = new Type[] {type, field.getFieldType(pData.cpgen)};
            else
                argType = new Type[] {type};
        }
        else
            return false;

        // Is this an instance item?
        if (pData.nodeObj.get(target.objName.text) != null)
        {
            ArrayList<String> superclassList = new ArrayList<String>();
            superclassList.add(type.toString());
            try
            {
                JavaClass[] superclass =
                        Repository.lookupClass(type.toString()).getSuperClasses();
                for (int i = 0; i < superclass.length; i++)
                {
                    if (pData.stateObj.contains(superclass[i].getClassName()))
                        superclassList.add(superclass[i].getClassName());
                }
            }
            catch (ClassNotFoundException ex)
            { /* Ignored for now */ }
            if (superclassList.contains(pData.nodeObj.get(target.objName.text)))
//            if (type.toString().equals(pData.nodeObj.get(target.objName.text)))
            {
                System.out.println("Found " + target.objName.text + " as target");
                pData.nodeObjIndex.put(target.objName.text, new Integer(0));
                return true;
            }
            else
                return false;
        }

        // See if the type matches (or that of any ancestor)
        if (matchesTypeAncestor(target.typeName, type.toString()))
            return true;

        // If the type is a superclass or [transitive] interface of the
        // type in the policy, there is a chance we're dealing with an upcasted
        // instance of that type. Inject an instanceof check to see.
        // (We do NOT do this for instances of java.lang.Object)

        if (!type.toString().equals("java.lang.Object") &&
                matchesTypeAncestor(type.toString(), target.typeName))
        {
            if (pData.instruction.getName().endsWith("static"))
                return false;
            // Code generation; not desired
            // TODO: Analyze injected code
//            if (pData.generateCode)
//                DynamicCodeBuilder.buildTargetCheck(target, pData, iBlock, argType);
            return true;
        }

        return false;

    }

    private static boolean matchesWithin(
            Within within,
            PointcutData pData)
    {
        // Checks the type of the class in which this instruction is executing

        if (pData.cgen == null)
            return false;

        return matchesTypeName(within.tname, pData.cgen.getClassName());

    }

    private static boolean matchesWithinCode(
            WithinCode withincode,
            PointcutData pData)
    {
        // Compare to the method in which this instruction is executing

        boolean isCP = true; // Tracks if this is *just* constructor patterns
        boolean retVal = true;

        if (pData.mgen == null)
            return false;

        // Check against each component; as soon as we hit something that
        // returns 'false', we jump out and return that
        // A 'true' returns only if EVERYTHING clears
        for (int i = 0; (i < withincode.mp.size() && retVal); i++)
        {
            MemberPattern mp = withincode.mp.get(i);
            if (mp instanceof Modifier)
                retVal = matchesModifier((Modifier)mp, pData.mgen.getModifiers());
            else if (mp instanceof ClassId)
                retVal = matchesClassId((ClassId)mp, Misc.constructType(pData.mgen.getClassName()));
            else if (mp instanceof MemberId)
            {
                if (!((MemberId)mp).mname.text.equalsIgnoreCase("new"))
                {
                    retVal = matchesMemberId((MemberId)mp, pData.mgen.getName());
                    isCP = false;
                }
            }
            else if (mp instanceof RetType)
            {
                retVal = matchesRetType((RetType)mp, pData.mgen.getReturnType());
                isCP = false;
            }
        }

        // If we didn't have a member name or return type, we were given a
        // sequence of constructor patterns, and so we return true ONLY
        // if the method name given was <init>
        if (isCP && retVal)
            retVal = (pData.mgen.getName().equals("<init>"));

        return retVal;

    }

    private static boolean matchesBooleanOp(
            BooleanOp bop,
            PointcutData pData)
    {
        // Which kind of bop are we working with?
        if (bop instanceof Not)
            return matchesNot((Not)bop, pData);
        else if (bop instanceof And)
            return matchesAnd((And)bop, pData);
        else if (bop instanceof Or)
            return matchesOr((Or)bop, pData);
        else
            return false;
    }

    private static boolean matchesNot(
            Not not,
            PointcutData pData)
    {
        // Just a negation of the match boolean for the next level down

        boolean retVal = false;

        // Make sure we know if there's any dynamic checks contained within
        if (not.p instanceof BooleanOp)
        {
            retVal = !matchesPointcut(not.p, pData);
            if (((BooleanOp)not.p).containsDynamicChecks)
                not.containsDynamicChecks = true;
        }
        else if (not.p instanceof DynamicPointcut)
        {
            not.containsDynamicChecks = true;
            retVal = !matchesPointcut(not.p, pData);
        }
        else
        {
            retVal = !matchesPointcut(not.p, pData);
        }

        if (not.containsDynamicChecks && !retVal)
            retVal = true; // Dynamic checks require this to return true

        return retVal;
    }

    private static boolean matchesAnd(
            And and,
            PointcutData pData)
    {
        // An and can contain any number of sub-pointcuts, so ALL of them
        // must return true in order for us to be able to return true here

        // Make sure we have something to look at
        if (and.p.isEmpty())
            return false;

        boolean retVal = true;

        boolean anyBopsWithDynamics = false; // Helps us know if we need to
                                             // insert any dynamic checks

        // As soon as retVal becomes false, this loop aborts
        for (int i = 0; (i < and.p.size() && retVal); i++)
        {
            // For the first time through, we only care about matches that
            // can be determined statically
            if (!(and.p.get(i) instanceof DynamicPointcut))
            {
                if (and.p.get(i) instanceof BooleanOp)
                {
                    retVal = matchesPointcut(and.p.get(i), pData);
                    if (((BooleanOp)and.p.get(i)).containsDynamicChecks)
                    {
                        anyBopsWithDynamics = true;
                        and.containsDynamicChecks = true;
                    }
                }
                else
                {
                    retVal = matchesPointcut(and.p.get(i), pData);
                }
            }
        }
        // If all the static checks evaluate to true, we start matching
        // with dynamic checks (TODO: Actually analyze the dynamic code)
        for (int i = 0; (i < and.p.size() && retVal); i++)
        {
            if (and.p.get(i) instanceof DynamicPointcut)
            {
                retVal = matchesPointcut(and.p.get(i), pData);
                // We used a dynamic check, so let that be known
                if (retVal)
                    and.containsDynamicChecks = true;
            }
        }

        if (!retVal)
            and.containsDynamicChecks = false; // Don't cascade up if dynamic
                                               // checks are unneeded

        return retVal;
    }

    private static boolean matchesOr(
            Or or,
            PointcutData pData)
    {
        // An or can contain any number of sub-pointcuts, so only ONE of them
        // has to return true for us to return a true here

        // Make sure we have something to look at
        if (or.p.isEmpty())
            return false;

        boolean retVal = false;

        boolean anyBopsWithDynamics = false; // Helps us know if we need to
                                             // insert any dynamic checks

        // As soon as retVal becomes true, it cannot be modified again
        // (But we keep going in case there's some buried dynamic checks)
        for (int i = 0; i < or.p.size(); i++)
        {
            boolean temp;
            if (!(or.p.get(i) instanceof DynamicPointcut))
            {
                if (or.p.get(i) instanceof BooleanOp)
                {
                    temp = matchesPointcut(or.p.get(i), pData);
                    if (!retVal)
                        retVal = temp;
                    if (((BooleanOp)or.p.get(i)).containsDynamicChecks)
                    {
                        anyBopsWithDynamics = true;
                        or.containsDynamicChecks = true;
                    }
                }
                else
                {
                    temp = matchesPointcut(or.p.get(i), pData);
                    if (!retVal)
                        retVal = temp;
                }
            }
        }
        // If all the static checks evaluate to false (or if they evaluated
        // to true but contained dynamic dependencies), we start matching
        // with dynamic checks (TODO: Analyze the dynamic checks)
        if (!retVal || anyBopsWithDynamics)
        {
            for (int i = 0; i < or.p.size(); i++)
            {
                boolean temp;
                if (or.p.get(i) instanceof DynamicPointcut)
                {
                    temp = matchesPointcut(or.p.get(i), pData);
                    if (temp)
                    {
                        retVal = true;
                        or.containsDynamicChecks = true;
                    }
                }
            }
        }

        if (!retVal)
            or.containsDynamicChecks = false; // Don't cascade up if dynamic
                                               // checks are unneeded

        return retVal;
    }

    private static boolean matchesAfter(
            After after,
            PointcutData pData)
    {
        // Recursively checks the previous command against the inner pointcut

        InstructionHandle prevIh = pData.ih.getPrev();

        // Obviously, there has to be a preceding command
        if (prevIh == null)
            return false;

        // Move over relevant pointcut data
        PointcutData newPData = new PointcutData();
        newPData.cgen = pData.cgen;
        newPData.cpgen = pData.cpgen;
        newPData.method = pData.method;
        newPData.mgen = pData.mgen;
        newPData.nodeObj = pData.nodeObj;
        newPData.stateObj = pData.stateObj;

        return PointcutMatcher.matchesPointcut(after.p,newPData);
    }

    private static boolean matchesModifier(
            Modifier modifier,
            Integer modifierInt)
    {

        // If pData contains a null modifiers value, we have no way of knowing
        // anything
        if (modifierInt == null)
            return false;

        // Check to see if the modifier name lines up with anything
        // in the pData modifier array
        if (matchesModifierName(modifier.mname, "abstract") &&
            (modifierInt & Constants.ACC_ABSTRACT) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "annotation") &&
            (modifierInt & Constants.ACC_ANNOTATION) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "bridge") &&
            (modifierInt & Constants.ACC_BRIDGE) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "enum") &&
            (modifierInt & Constants.ACC_ENUM) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "final") &&
            (modifierInt & Constants.ACC_FINAL) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "interface") &&
            (modifierInt & Constants.ACC_INTERFACE) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "native") &&
            (modifierInt & Constants.ACC_NATIVE) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "private") &&
            (modifierInt & Constants.ACC_PRIVATE) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "protected") &&
            (modifierInt & Constants.ACC_PROTECTED) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "public") &&
            (modifierInt & Constants.ACC_PUBLIC) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "static") &&
            (modifierInt & Constants.ACC_STATIC) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "strict") &&
            (modifierInt & Constants.ACC_STRICT) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "super") &&
            (modifierInt & Constants.ACC_SUPER) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "synchronized") &&
            (modifierInt & Constants.ACC_SYNCHRONIZED) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "synthetic") &&
            (modifierInt & Constants.ACC_SYNTHETIC) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "transient") &&
            (modifierInt & Constants.ACC_TRANSIENT) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "varargs") &&
            (modifierInt & Constants.ACC_VARARGS) != 0)
            return true;
        if (matchesModifierName(modifier.mname, "volatile") &&
            (modifierInt & Constants.ACC_VOLATILE) != 0)
            return true;

        // If everything above failed, return false
        return false;

    }

    private static boolean matchesClassId(
            ClassId classId,
            Type classType)
    {

        // We need a class type to know anything
        if (classType == null)
            return false;

        return (matchesTypeName(classId.tname, classType.toString()));

    }

    private static boolean matchesMemberId(
            MemberId memberId,
            String memberName)
    {

        // We need a member name to know anything
        if (memberName == null)
            return false;

        return (matchesMemberName(memberId.mname, memberName));

    }

    private static boolean matchesRetType(
            RetType retType,
            Type type)
    {

        // We need a return type to know anything
        if (type == null)
            return false;

        return (matchesTypeName(retType.tname, type.toString()));

    }

    private static boolean matchesModifierName(
            ModifierName mname,
            String text)
    {
        return matchesText(mname.text, text);
    }

    private static boolean matchesTypeName(
            TypeName tname,
            String text)
    {
        String parentText = tname.text;
        boolean checkDescendants = false;
        if (parentText.endsWith("+"))
        {
            parentText = parentText.substring(0, parentText.length()-1);
            checkDescendants = true;
        }
        if (!checkDescendants)
            return matchesText(convertTypePatternToRegex(tname.text), text);
        else
        {
            JavaClass jclass = null;
            try
            {
                jclass = Repository.lookupClass(text);
                if (matchesText(convertTypePatternToRegex(parentText), jclass.getClassName()))
                    return true;
                if (!jclass.getClassName().equals("java.lang.Object"))
                    if (matchesTypeName(tname, jclass.getSuperclassName()))
                        return true;
                String[] interfaceName = jclass.getInterfaceNames();
                for (int i = 0; i < interfaceName.length; i++)
                {
                    if (matchesTypeName(tname, interfaceName[i]))
                        return true;
                }
                return false;
            }
            catch (ClassNotFoundException ex)
            { return matchesText(convertTypePatternToRegex(parentText), text); }
        }
    }

    private static boolean matchesMemberName(
            MemberName mname,
            String text)
    {
        return matchesText(mname.text, text);
    }

    private static boolean matchesInstrName(
            InstrName iname,
            String text)
    {
        return matchesText(iname.text, text);
    }

    private static boolean matchesText(String pattern, String text)
    {
        Pattern p = new Pattern(pattern);
        return p.contains(text);
    }

    /**
     * Converts a type pattern expression to a jrexx-compatible
     * regular expression. Uses rules consistent with those in the AspectJ
     * manual. NOTE: Empty strings are treated as wild, so "" becomes ".*".
     * @param tp The type pattern.
     * @return A normal regex which is functionally equivalent to the input.
     */
    private static String convertTypePatternToRegex(String tp)
    {
        if (tp.equals("*") || tp.isEmpty())
            return ".*";

        String rgx = tp;

        for (int i = 0; i < rgx.length(); i++)
        {
            if (rgx.charAt(i)=='.')
            {
                if (i < rgx.length()-1)
                {
                    if (rgx.charAt(i+1)!='.')
                    {
                        rgx = rgx.substring(0,i)+"\\."+rgx.substring(i+1);
                        i = i + 1;
                    }
                    else
                    {
                        // Skip over a character (we hit a "..")
                        i = i + 1;
                    }
                }
                else
                {
                    rgx = rgx.substring(0,i)+"\\.";
                    i = i + 1;
                }
            }
        }

        rgx = rgx.replaceAll("\\*", "((.\\*)&!(.\\*(\\\\.).\\*))");
        rgx = rgx.replaceAll("\\.\\.", "((\\\\..\\*\\\\.)|(\\\\.))");

        return rgx;
    }

}