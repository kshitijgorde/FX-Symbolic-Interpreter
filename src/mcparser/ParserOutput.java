package mcparser;

import java.io.*;
import java.util.*;
import javax.swing.JOptionPane;

public class ParserOutput
{
    private static File outFile = null;
    private static HashMap<String,String> universeMap = new HashMap<String,String>();
    private static HashMap<String,Integer> universeNumWritesMap = new HashMap<String,Integer>();
    private static ArrayList<String> recursiveMethods = new ArrayList<String>();
    private static ArrayList<String> syncMethods = new ArrayList<String>();
    private static boolean isDirty = true;

    public static void setOutFile(String filename)
    {
        outFile = new File(filename);
    }

    public static boolean setUniverse(String instrHash, String universe)
    {
        if (universeMap.get(instrHash)!=null)
            if (universeMap.get(instrHash).equals(universe))
                return false;
        universeMap.put(instrHash, universe);
        if (universeNumWritesMap.containsKey(instrHash))
            universeNumWritesMap.put(instrHash, universeNumWritesMap.get(instrHash)+1);
        else
            universeNumWritesMap.put(instrHash, 1);
        isDirty = true;
        return true;
    }

    public static void setRecursiveMethod(String className, String methodName, String methodSig)
    {
        recursiveMethods.add(className+"."+methodName+methodSig);
        isDirty = true;
    }

    public static void setSyncMethod(String className, String methodName, String methodSig)
    {
        syncMethods.add(className+"."+methodName+methodSig);
        isDirty = true;
    }

    public static String getUniverse(String instrHash)
    {
        return universeMap.get(instrHash);
    }

    public static void dump(String varMaps) throws IOException
    {
        if (!isDirty)
            return;
        FileWriter outWriter = new FileWriter(outFile);
        // First define the recursive methods
        outWriter.write(recursiveMethods.toString().
                replace("[","").replace("]","\n").replace(",","\n").replace(" ",""));
        outWriter.write("%");
        // Second define the sync methods
        outWriter.write(syncMethods.toString().
                replace("[","").replace("]","\n").replace(",","\n").replace(" ",""));
        outWriter.write("%");
        // Finally put in the var maps
        if (varMaps.contains(", "))
            varMaps = varMaps.substring(2,varMaps.length()-1);
        String[] varMapArray = varMaps.split(", ");
        Iterator<String> iter = universeMap.keySet().iterator();
        while (iter.hasNext())
        {
            String hash = iter.next();
            String output = universeMap.get(hash);
            // Replace variables according to varMaps
            for (String varMapElem : varMapArray)
            {
                String newString =
                        varMapElem.substring(1,varMapElem.lastIndexOf(","));
                String oldString =
                        varMapElem.substring(varMapElem.lastIndexOf(",")+1,varMapElem.length()-1);
                output = output.replace(oldString,newString);
            }
            outWriter.write(hash+'\n'+output+"\n\n"+universeNumWritesMap.get(hash)+"\n%");
        }
        outWriter.close();
        isDirty = false;
    }
}
