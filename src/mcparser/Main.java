package mcparser;

import java.net.URLClassLoader;

public class Main
{

    public static void main(String[] args) throws ClassNotFoundException
    {
        try
        {
            JarProcessor jar = new JarProcessor("VerTest_update.jar");
            //ClassParser.getClassData(jar);
        }
        catch (Exception ex)
        {
            ex.printStackTrace();
        }
    }

}
