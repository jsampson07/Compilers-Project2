import ir.IRInstruction;
import ir.operand.IRVariableOperand;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.ArrayList;

public class IRNode {
    //Each node is a list of instrucs and has predecessors/successors
    //Every node/block also has its own GEN, KILL, etc sets
        //these sets use HashSet, and use varName and lineNumber to ensure uniqueness
    public IRInstruction instruction;
    public String defined_var = null;
    public List<String> used_vars = new ArrayList<>();
    public List<IRNode> predecessors = new ArrayList<>();
    public List<IRNode> successors = new ArrayList<>();
    public Set<IRNode> GEN = new HashSet<>();
    public Set<IRNode> KILL = new HashSet<>();
    public Set<IRNode> IN = new HashSet<>();
    public Set<IRNode> OUT = new HashSet<>();
    public boolean is_marked = false;


    // If we initialize without any parameters, just leave everything empty

    public IRNode() {}

    public IRNode(IRInstruction instruction) {
        this.instruction = instruction;
        switch(instruction.opCode) {
            case ASSIGN, ADD, SUB, MULT, DIV, AND, OR, CALLR, ARRAY_LOAD -> {
                this.defined_var = ((IRVariableOperand) instruction.operands[0]).getName();
            }
            default -> {
                break;
            }
        }
        for (int i = 1; i < this.instruction.operands.length; i++) {
            if (instruction.operands[i] instanceof IRVariableOperand) {
                used_vars.add(((IRVariableOperand) instruction.operands[i]).getName());
            }
        }
        // we need these special cases because the first operand is a use
        switch(instruction.opCode) {
            case ARRAY_STORE, RETURN -> {
                if (instruction.operands[0] instanceof IRVariableOperand) {
                    used_vars.add(((IRVariableOperand) instruction.operands[0]).getName());
                }
            }
            default -> {
                break;
            }
        }
    }

   public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if ((o == null) || (getClass() != o.getClass())) {
            return false;
        }
        IRNode irNode = (IRNode) o;
        return this.instruction.irLineNumber == irNode.instruction.irLineNumber;
    }

    public int hashCode() {
        return Objects.hash(this.instruction.irLineNumber);
    }

    // For testing purposes
    public String toString() {
        if (this.instruction.operands.length == 3) {
            return this.instruction.opCode.toString() + " " + this.instruction.operands[0] + " <- " + this.instruction.operands[1] + ", " + this.instruction.operands[2];
        } else if (this.instruction.operands.length == 2) {
            return this.instruction.opCode.toString() + " " + this.instruction.operands[0] + " <- " + this.instruction.operands[1];
        } else if (this.instruction.operands.length == 1) {
            return this.instruction.opCode.toString() + " " + this.instruction.operands[0];
        }
        return "";
    }

    public void addToGen(IRNode node) {
        this.GEN.add(node);
    }
    public void addToKill(IRNode node) {
        this.KILL.add(node);
    }
    public void addToOut(IRNode node) {
        this.OUT.add(node);
    }
}