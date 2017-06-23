package mcparser;

import java.io.*;
import java.util.*;
import java.util.jar.*;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;
import org.apache.bcel.Repository;
import org.apache.bcel.util.*;
import org.apache.bcel.Constants;

public class JarProcessor
{

    // Constants
    public static final String FILE_SEPARATOR = System.getProperty("file.separator");
    public static final String PATH_SEPARATOR = System.getProperty("path.separator");
    public static final String LINE_SEPARATOR = System.getProperty("line.separator");

    // Class fields
    private File file;
    private JarFile jarfile;
    public HashMap<String, ClassGen> classMap = new HashMap<String, ClassGen>();
    public HashMap<ClassGen, MethodGen> staticMethodMap = new HashMap<ClassGen,MethodGen>();
    public HashMap<ClassGen, FieldGen[]> staticFieldMap = new HashMap<ClassGen,FieldGen[]>();
    public ClassGen entryClass;
    public MethodGen entryMethod;

    public HashMap<String,ArrayList<String>> implementsMap = new HashMap<String,ArrayList<String>>();

    public JarProcessor(String filename)
            throws IOException, ClassNotFoundException
    {
        // Initialize vars
        file = new File(filename);
        jarfile = new JarFile(file);

        // Extract the JAR

        // Get the manifest classpath
        String manifestClassPath = jarfile.getManifest().getMainAttributes().getValue("Class-Path");
        if (manifestClassPath == null || manifestClassPath.trim().isEmpty())
            manifestClassPath = "";
        else
            manifestClassPath = file.getParent() + FILE_SEPARATOR +
                        manifestClassPath.trim().
                        replace(".jar ", ".jar" + PATH_SEPARATOR + file.getParent() + FILE_SEPARATOR).
                        replace("/", FILE_SEPARATOR);

        // Recursively acquire information from all JARs in the classpath
        String[] jarPaths = manifestClassPath.split(";");
        for (String jarPath : jarPaths)
        {
            if (!jarPath.trim().isEmpty())
            {
                JarProcessor jarProcessor = new JarProcessor(jarPath);
                this.classMap.putAll(jarProcessor.classMap);
                this.staticFieldMap.putAll(jarProcessor.staticFieldMap);
                this.staticMethodMap.putAll(jarProcessor.staticMethodMap);
                for (String implementedClass : jarProcessor.implementsMap.keySet())
                {
                    if (this.implementsMap.containsKey(implementedClass))
                        this.implementsMap.get(implementedClass).addAll(jarProcessor.implementsMap.get(implementedClass));
                    else
                        this.implementsMap.put(implementedClass, jarProcessor.implementsMap.get(implementedClass));
                }
            }
        }

        // Set the repository
        Repository.clearCache();
        Repository.setRepository(SyntheticRepository.getInstance(
                new ClassPath(
                    (file.getAbsolutePath() +
                    (manifestClassPath.isEmpty() ? "" : (";" + manifestClassPath))))));
//        javax.swing.JOptionPane.showMessageDialog(null,"Class path:\n" +
//                Repository.getRepository().getClassPath().toString());
        System.out.println("Class path:\n" +
                Repository.getRepository().getClassPath().toString());

        // If there's a main, get it
        String entryClassName =
               jarfile.getManifest().getMainAttributes().getValue(java.util.jar.Attributes.Name.MAIN_CLASS);
        if (entryClassName != null)
        {
            entryClass =
                    new ClassGen(Repository.lookupClass(entryClassName));
            Method[] mainCgenMethods = entryClass.getMethods();
            for (int i = 0; i < mainCgenMethods.length; i++)
            {
                if (mainCgenMethods[i].getName().equals("main"))
                    entryMethod = new MethodGen(mainCgenMethods[i],entryClassName,entryClass.getConstantPool());
            }
        }

        // Extract entires
        Enumeration entries = jarfile.entries();
        
        while (entries.hasMoreElements())
        {
            JarEntry entry = (JarEntry)entries.nextElement();

            System.out.println("Extracting file: " + entry.getName());

            InputStream is = jarfile.getInputStream(entry);

            if (entry.getName().endsWith(".class"))
            {

                JavaClass jclass = new org.apache.bcel.classfile.ClassParser(
                            is, entry.getName()).parse();
                ClassGen cgen = new ClassGen(jclass);
                // Is there a static initializer?
                Method[] cgenMethods = cgen.getMethods();
                for (int i = 0; i < cgenMethods.length; i++)
                {
                    if (cgenMethods[i].getName().equals("<clinit>"))
                    {
                        MethodGen staticMethod =
                                new MethodGen(cgenMethods[i],cgen.getClassName(),cgen.getConstantPool());
                        staticMethodMap.put(cgen, staticMethod);
                    }
                }
                // Any static fields to initialize?
                Field[] cgenFields = cgen.getFields();
                ArrayList<FieldGen> cgenFieldGens = new ArrayList<FieldGen>();
                for (int i = 0; i < cgenFields.length; i++)
                {
                    if (cgenFields[i].isStatic())
                        cgenFieldGens.add(new FieldGen(cgenFields[i],cgen.getConstantPool()));
                }
                FieldGen[] cgenFieldGenArray = new FieldGen[cgenFieldGens.size()];
                cgenFieldGens.toArray(cgenFieldGenArray);
                staticFieldMap.put(cgen, cgenFieldGenArray);
                // Finally, put the classgen into our master list/map (Currently just storing class names, not cgens)
                classMap.put(cgen.getClassName(), null);
            }

            is.close();
        }

        jarfile.close();
        System.out.println("Finished reading " + jarfile.getName());

        // Set up the implements map
        for (String classname : classMap.keySet())
        {
            JavaClass jclass = Repository.lookupClass(classname);
            for (JavaClass superClass : jclass.getSuperClasses())
            {
                String superClassName = superClass.getClassName();
                if (!implementsMap.containsKey(superClassName))
                    implementsMap.put(superClassName, new ArrayList<String>());
                implementsMap.get(superClassName).add(jclass.getClassName());
            }
            for (JavaClass implementedClass : jclass.getAllInterfaces())
            {
                String implementedClassName = implementedClass.getClassName();
                if (!implementsMap.containsKey(implementedClassName))
                    implementsMap.put(implementedClassName, new ArrayList<String>());
                implementsMap.get(implementedClassName).add(jclass.getClassName());
            }
        }

    }

    public void dumpImplementsMap(String filename)
            throws IOException
    {
        // Dumps the implementsMap to a text file in prolog rule format
        FileWriter out = new FileWriter(filename);
        for (String implementedClassName : implementsMap.keySet())
        {
            for (String implementorClassName : implementsMap.get(implementedClassName))
            {
                out.write("implemented_by('"+implementedClassName+"','"+implementorClassName+"').\n");
            }
        }
        out.close();
    }

}
