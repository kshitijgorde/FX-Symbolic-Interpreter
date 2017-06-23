package mcparser.instr;

import mcparser.*;
import mcparser.util.*;

import java.util.*;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;

public class FieldOpData
{

    public ReferenceType objType = null;
    public String fieldName = null;
    public Type fieldType = null;
    public String signature = null;
    public int modifiers = 0;
    public String opname = null;
    public ClassGen cgen = null;
    public FieldGen fgen = null;

}
