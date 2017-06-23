package mcparser;

import java.util.*;
import mcparser.util.*;
import org.apache.bcel.Repository;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;

public class ClassParser
{

    public static ClassGen[] getClassData(JarProcessor jar)
    {
        ClassGen[] classGenArray = new ClassGen[jar.classMap.size()];
        Iterator<String> classIter = jar.classMap.keySet().iterator();
        int i = 0;
        while (classIter.hasNext())
        {
            classGenArray[i] = jar.classMap.get(classIter.next());
//            MethodGen methodGen = new MethodGen(
//                    classGenArray[i].getMethodAt(0),
//                    classGenArray[i].getClassName(),
//                    classGenArray[i].getConstantPool());
//            System.out.println(methodGen.getInstructionList().toString());
            i++;
        }
        return classGenArray;
    }

    public static MethodData[] getMethodData(ClassGen classGen)
    {
        Method[] methods = classGen.getMethods();
        MethodData[] methodData = new MethodData[methods.length];
        for (int i = 0; i < methods.length; i++)
        {
            MethodGen methodGen = new MethodGen(
                    methods[i],
                    classGen.getClassName(),
                    classGen.getConstantPool());
            methodData[i] = new MethodData();
            methodData[i].name = methodGen.getName();
            methodData[i].args = methodGen.getArgumentTypes();
            methodData[i].exceptions = methodGen.getExceptions();
            methodData[i].returnType = methodGen.getReturnType();
            methodData[i].instructions =
                    methodGen.getInstructionList().getInstructionHandles();
            methodData[i].localVariables = methodGen.getLocalVariables();
        }
        return methodData;
    }

    public static MethodGen[] createMethodGenArray(ClassGen cgen)
    {
        Method[] methodArray = cgen.getMethods();
        MethodGen[] mgenArray = new MethodGen[methodArray.length];
        for (int i = 0; i < methodArray.length; i++)
        {
            mgenArray[i] = new MethodGen(
                    methodArray[i],cgen.getClassName(),cgen.getConstantPool());
        }
        return mgenArray;
    }

    public static Type[] getLocalVariableTypes(
            ClassGen cgen,
            MethodGen mgen)
    {
        LocalVariableGen[] lvgenArray = mgen.getLocalVariables();
        Type[] lvTypeArray = new Type[lvgenArray.length];
        for (int i = 0; i < lvgenArray.length; i++)
        {
            lvTypeArray[i] = lvgenArray[i].getType();
        }
        return lvTypeArray;
    }

    // If c1 is a superclass of c2, returns c1. If c2 is a superclass
    // of c1, returns c2. If neither is a superclass of the other,
    // returns null.
    public static JavaClass isSuperclass(JavaClass c1, JavaClass c2)
            throws ClassNotFoundException
    {
        JavaClass[] c1Supers = c1.getSuperClasses();
        JavaClass[] c2Supers = c2.getSuperClasses();
        JavaClass[] c1Interfaces = c1.getAllInterfaces();
        JavaClass[] c2Interfaces = c2.getAllInterfaces();

        for (JavaClass jc : c1Supers)
        {
            if (jc.equals(c2))
                return c2;
        }
        for (JavaClass jc : c2Supers)
        {
            if (jc.equals(c1))
                return c1;
        }
        for (JavaClass jc : c1Interfaces)
        {
            if (jc.equals(c2))
                return c2;
        }
        for (JavaClass jc : c2Interfaces)
        {
            if (jc.equals(c1))
                return c1;
        }
        return null;
    }

    // If m1 is overloaded by m2, returns c1. If m2 is overloaded
    // by m1, returns c2. If neither overloads the other, returns null.
    public static JavaClass isOverloaded(
            JavaClass c1, JavaClass c2, Method m1, Method m2)
            throws ClassNotFoundException
    {

        if (m1.getName().equals(m2.getName()) &&
            m1.getSignature().equals(m2.getSignature()))
        {
            JavaClass superClass = isSuperclass(c1,c2);
            if (superClass == null)
                return null;
            else if (superClass.equals(c1))
                return c1;
            else if (superClass.equals(c2))
                return c2;
        }
        return null;
    }

    public static String isOverloaded(
            String c1Name, String c2Name, String m1Sig, String m2Sig)
            throws ClassNotFoundException
    {

        JavaClass c1 = Repository.lookupClass(c1Name);
        JavaClass c2 = Repository.lookupClass(c2Name);

        Method m1 = Misc.getMethodGen(c1,m1Sig).getMethod();
        Method m2 = Misc.getMethodGen(c2,m2Sig).getMethod();

        JavaClass retJC = isOverloaded(c1,c2,m1,m2);

        if (retJC == null)
            return null;
        else if (retJC.getClassName().equals(c1Name))
            return c1Name;
        else if (retJC.getClassName().equals(c2Name))
            return c2Name;
        return null;
    }
}
