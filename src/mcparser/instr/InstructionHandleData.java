package mcparser.instr;

import org.apache.bcel.generic.*;

public class InstructionHandleData
{
    public ClassGen cgen;
    public MethodGen mgen;
    public Instruction instruction;
    public int offset;
    public String instructionString;

    public InstructionHandleData(ClassGen cgen, MethodGen mgen, InstructionHandle ih)
    {
        this.cgen = cgen;
        this.mgen = mgen;
        ConstantPoolGen cpgen = cgen.getConstantPool();
        this.offset = ih.getPosition();
        this.instruction = ih.getInstruction();
        this.instructionString = instruction.toString(cpgen.getConstantPool());
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final InstructionHandleData other = (InstructionHandleData) obj;
        if (this.cgen != other.cgen && (this.cgen == null || !this.cgen.equals(other.cgen))) {
            return false;
        }
        if (this.mgen != other.mgen && (this.mgen == null || !this.mgen.equals(other.mgen))) {
            return false;
        }
        if (this.offset != other.offset) {
            return false;
        }
        if ((this.instructionString == null) ? (other.instructionString != null) : !this.instructionString.equals(other.instructionString)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 59 * hash + (this.cgen != null ? this.cgen.hashCode() : 0);
        hash = 59 * hash + (this.mgen != null ? this.mgen.hashCode() : 0);
        hash = 59 * hash + this.offset;
        hash = 59 * hash + (this.instructionString != null ? this.instructionString.hashCode() : 0);
        return hash;
    }


}
