package mcparser.util;

/*
 * Miscellaneous utility methods
 */

import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;
import org.apache.bcel.util.*;
import org.apache.bcel.Constants;
import org.apache.bcel.Repository;

import spox.util.*;
import spox.policy.*;

public class Misc
{

    /**
     * Checks to see if a particular object is contained within an array.
     * @param array The array (of Objects) to be checked.
     * @param value The object.
     * @return True if the array contains the object, false otherwise.
     */
    public static boolean arrayContains(Object[] array, Object value)
    {
        // Utility method
        // Simply returns true if value is contained within array, false if not
        
        for (int i = 0; i < array.length; i++)
        {
            if (array[i].equals(value))
                return true;
        }
        
        return false;
    }
    
    public static boolean componentArrayContainsName(
            ArrayList<PolicyComponent.Component> component, String name)
    {
        for (int i = 0; i < component.size(); i++)
        {
            if (component.get(i).name.equals(name))
                return true;
        }
        return false;
    }

    /**
     * Uses the Repository information to determine if a class is available
     * @return True if the class is in the repository, False otherwise.
     */
    public static boolean classExists(String className)
    {
        try
        {
            Repository.lookupClass(className);
            return true;
        }
        catch (ClassNotFoundException ex)
        {
            return false;
        }
    }

    public static String[] toStringArray(Object[] array)
    {
        // Converts a given array of objects to an array of strings
        // using each object's toString() method
        
        String[] stringArray = new String[array.length];
        
        for (int i = 0; i < array.length; i++)
            stringArray[i] = array[i].toString();
        
        return stringArray;
    }
    
    public static boolean instanceofAny (java.lang.reflect.Type[] classArray, Object object)
    {
        // Reports whether the given object is an instance of any of the
        // classes in classArray
        
        for (int i = 0; i < classArray.length; i++)
        {
            if (object.getClass().equals(classArray[i]))
                return true;
        }
        
        return false;
    }

    /**
     * Given a class name, constructs a corresponding type.
     * @param className The name of the class for which we need a type.
     * @return The type.
     */
    public static Type constructType (String className)
    {
        String sig = "L" + className.replace('.','/').replace("[]", "") + ";";
        while (className.endsWith("[]"))
        {
            sig = "[" + sig;
            className = className.substring(0, className.length()-2);
        }
        return Type.getType(sig);
    }
    
    /**
     * Given an array of class names, constructs a corresponding type array.
     * @param className An array of class names.
     * @return An array of types.
     */
    public static Type[] constructType (String[] className)
    {
        Type[] type = new Type[className.length];
        for (int i = 0; i < className.length; i++)
            type[i] = constructType(className[i]);
        return type;
    }
    
    /**
     * Given a JavaClass object and a method signature (name+sig), retrieves the
     * corresponding Method object. If the method is not found,
     * all superclasses are searched until it is. If the method is STILL
     * not found, null is returned.
     * @param javaClass The class containing the method.
     * @param methodSig The method's signature.
     * @return The Method object, or null if not found.
     */
    public static MethodGen getMethodGen (JavaClass javaClass, String methodSig)
            throws ClassNotFoundException
    {
        Method[] methodArray = javaClass.getMethods();
        for (int i = 0; i < methodArray.length; i++)
        {
            if ((methodArray[i].getName() + methodArray[i].getSignature()).equals(methodSig))
            {
                ClassGen cgen = new ClassGen(javaClass);
                return new MethodGen(methodArray[i],cgen.getClassName(),cgen.getConstantPool());
            }
        }
        if (javaClass.getClassName().equals("java.lang.Object"))
            return null;
        javaClass = javaClass.getSuperClass();
        return getMethodGen(javaClass,methodSig);
    }

    /**
     * Given a JavaClass object and a field signature, retrieves the
     * corresponding Field object. If the field is not found,
     * all superclasses are searched until it is. If the field is STILL
     * not found, null is returned. Note that if a superclass is entered,
     * javaClass will be changed to match it. That is,
     * this method is NOT without side effects to javaClass.
     * @param javaClass The class containing the field. May be changed.
     * @param fieldSig The field's signature.
     * @return The Method object, or null if not found.
     */
    public static Field getField (JavaClass javaClass, String fieldSig)
            throws ClassNotFoundException
    {
        Field[] fieldArray = javaClass.getFields();
        for (int i = 0; i < fieldArray.length; i++)
        {
            if ((fieldArray[i].getName() + fieldArray[i].getSignature()).equals(fieldSig))
                return fieldArray[i];
        }
        if (javaClass.getClassName().equals("java.lang.Object"))
            return null;
        javaClass = javaClass.getSuperClass();
        return getField(javaClass,fieldSig);
    }

}        

