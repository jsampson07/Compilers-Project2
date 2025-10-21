import ir.IRFunction;
import ir.IRInstruction;
import ir.operand.IRLabelOperand;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

public class IRcfg {
    //public IRNode entry_node; // the entry node for the CFG (i.e. head)
    public List<IRNode> nodes = new ArrayList<>(); // list of nodes in the graph (each are individual instrucs; in order when "executing" code)

    public IRcfg() {}

    public IRcfg(IRFunction function) {
        Map<Integer, IRNode> irInstrucToNode = new HashMap<>();
        Map<String, IRNode> irLabelToNode = new HashMap<>();
        //public Map<String, IRNode> irFunctionToNode = new HashMap();

        // first pass: create a node for each instruction, then we can work off the nodes rather than instructions
        for (IRInstruction instruction : function.instructions) {
            IRNode new_node = new IRNode(instruction);
            irInstrucToNode.put(instruction.irLineNumber, new_node);

            if (instruction.opCode == IRInstruction.OpCode.LABEL) { // this instruction is a label, lets add it for easy data flow
                String label_name = ((IRLabelOperand) instruction.operands[0]).getName();
                irLabelToNode.put(label_name, irInstrucToNode.get(instruction.irLineNumber));
            }
        }

        // now that I have the nodes of the graph, i need to connect them to represent the data flow correctly
        IRInstruction curr_instruction = null;
        IRNode curr_node = null;
        List<IRInstruction> instructions = function.instructions;
        for (int i = 0; i < instructions.size(); i++) {
            curr_instruction = instructions.get(i);
            curr_node = irInstrucToNode.get(curr_instruction.irLineNumber);
            //now that we have the node, we can actually connect nodes when we find the data flow (branch, goto, regular instruction)
            switch (curr_instruction.opCode) {
                case GOTO -> {
                    String goto_label = ((IRLabelOperand) curr_instruction.operands[0]).getName();
                    IRNode target_node = irLabelToNode.get(goto_label);
                    connectNodes(curr_node, target_node);
                }
                //BRANCH CASES: we need to make a target_node for jumping to label AND for just going to next-line (condition is not met)
                case BREQ, BRNEQ, BRLT, BRGT, BRGEQ -> {
                    //if we were to take the branch
                    String branch_label = ((IRLabelOperand) curr_instruction.operands[0]).getName();
                    IRNode target_node1 = irLabelToNode.get(branch_label);
                    connectNodes(curr_node, target_node1);
                    //if we didn't take the branch, we just go to the next instruction
                    if (i + 1 < instructions.size()) {
                        IRInstruction next_instruc = instructions.get(i + 1);
                        IRNode target_node2 = irInstrucToNode.get(next_instruc.irLineNumber); //curr instruc, we just want next instruc (node)
                        connectNodes(curr_node, target_node2);
                    }
                }
                case RETURN -> {
                    break;
                }
                default -> { //everything else including CALL, CALLR
                    if (i + 1 < instructions.size()) {
                        IRInstruction next_instruc = instructions.get(i + 1);
                        IRNode target_node = irInstrucToNode.get(next_instruc.irLineNumber);
                        connectNodes(curr_node, target_node);
                    }
                }
            }
            this.nodes.add(curr_node); // add this to the list of nodes after all info needed for it
        }
    }

    public void addToCFG(IRNode node) {
        this.nodes.add(node);
    }

    public void connectNodes(IRNode from, IRNode to) {
        from.successors.add(to);
        to.predecessors.add(from);
    }
}