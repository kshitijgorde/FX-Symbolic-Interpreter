import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.util.ClassPath.ClassFile;
import mcparser.ClassCache;

class ConstantPoolOperation{

	 public static ConstantPool getConstantPoolFromClass(String className){
	   try {
           JavaClass jclass = ClassCache.getClass(className);
           System.out.println(jclass);
           return jclass.getConstantPool();
       }
       catch (ClassNotFoundException ex) {
           System.out.println(ex);
           return null;
       }
   }

   	public static void main(String[] args){
   		ConstantPool cp = getConstantPoolFromClass("HelloWorld.java");
   		System.out.println(cp);
   	}

}