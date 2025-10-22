import ir.*;
import ir.IRInstruction.OpCode;
import ir.datatype.IRArrayType;
import ir.datatype.IRIntType;
import ir.datatype.IRType;
import ir.operand.IRConstantOperand;
import ir.operand.IRLabelOperand;
import ir.operand.IROperand;
import ir.operand.IRVariableOperand;
import main.java.mips.MIPSInstruction;
import main.java.mips.MIPSOp;
import main.java.mips.MIPSProgram;
import main.java.mips.operand.Addr;
import main.java.mips.operand.Imm;
import main.java.mips.operand.MIPSOperand;
import main.java.mips.operand.Register;
import java.util.List;
import java.util.ArrayList;

import java.io.PrintStream;
import java.util.*;

int curr_line_num = 0;

public class Demo {
    public static void main(String[] args) throws Exception {
        // Parse the IR file
        IRReader irReader = new IRReader();

        /* IRProgram -> IRFunction -> (IRVariableOperand and IRInstruction) -> [IRInstruction] ==> (OpCode, IROperand) */
        IRProgram program = irReader.parseIRFile(args[0]); //Work on this object

        for (IRFunction function : program.functions) {
            IRcfg cfg = new IRcfg(function); // we create the CFG for this function
            // now we want to run the optimizer
            /* Reaching Definitions Analysis 
                    We want to go through each node and then set the GEN and KILL sets
                    AND we want to initialize OUT = GEN and IN = null
                    THEN we want to do a SECOND PASS:
                        - where we calculate the IN and OUT sets UNTIL we reach a fixed point (IN/OUT sets are equal after 2 iterations) */
            
            //1. Calculate GEN/KILL Sets and Initialize OUT set = GEN
            calculateSets(cfg);

            //2. Calculate IN/OUT Sets
            fixedPointAlg(cfg);

            /* USED FOR TESTING AND CHECKING SETS for the nodes after calculating them
            for (IRNode node : cfg.nodes) {
                System.out.println("GEN[node]: " + node.GEN);
                System.out.println("KILL[node]: " + node.KILL);
                System.out.println("IN[node]: " + node.IN);
                System.out.println("OUT[node]: " + node.OUT);
            }
            */

            //3. Mark Algorithm
                //a. mark critical instructions
            markAlg(cfg);

            //4. Sweep Algorithm and get the critical instructions and update the functions instructions list
            sweepAlg(cfg, function);
        }

        // we have our optimized IR so now...
        /* 
        We want to conduct instruction selection stage
            1) Parse optimized IR program to turn into MIPS .s file
            2) For each function...
                - Loop through each instruction and generate MIPS one-by-one
            3) 
         */

        MIPSProgram mips_program = new MIPSProgram(null, null, null);
        for (IRFunction function : program.functions) {
            instruction_selector(function, mips_program);
        }

        // Print the IR to another file
        IRPrinter filePrinter = new IRPrinter(new PrintStream(args[1]));
        filePrinter.printProgram(program);

        // Create an IR printer that prints to stdout
        IRPrinter irPrinter = new IRPrinter(new PrintStream(System.out));

        // Print all instructions that stores a constant to an array
        System.out.println("Instructions that stores a constant to an array:");
        // Implement the algorithm here
        for (IRFunction function : program.functions) { // for each function in our program
            for (IRInstruction instruction : function.instructions) { // we go through every instruction
                //This is specific to the Demo (I think)
                if (instruction.opCode == IRInstruction.OpCode.ARRAY_STORE) {
                    if (instruction.operands[0] instanceof IRConstantOperand) {
                        System.out.print(String.format("Line %d:", instruction.irLineNumber));
                        irPrinter.printInstruction(instruction);
                    }
                }
            }
        }
        System.out.println();

        // Print the name of all int scalars and int arrays with a size of 1
        System.out.println("Int scalars and 1-sized arrays:");
        for (IRFunction function : program.functions) {
            List<String> vars = new ArrayList<>();
            for (IRVariableOperand v : function.variables) {
                IRType type = v.type;
                // For each unique data type, only one IRType object will be created
                // so that IRType objects can be compared using '=='
                if (type == IRIntType.get() || type == IRArrayType.get(IRIntType.get(), 1))
                    vars.add(v.getName());
            }
            if (!vars.isEmpty())
                System.out.println(function.name + ": " + String.join(", ", vars));
        }
        System.out.println();

        // Print all variables that are declared but not used (including unused parameters)
        System.out.println("Unused variables/parameters:");
        for (IRFunction function : program.functions) {
            // IROperand objects are not shared between instructions/parameter list/variable list
            // They should be compared using their names
            Set<String> vars = new HashSet<>();
            // Parameters are not included in the variable list
            for (IRVariableOperand v : function.parameters)
                vars.add(v.getName());
            for (IRVariableOperand v : function.variables)
                vars.add(v.getName());
            for (IRInstruction instruction : function.instructions)
                for (IROperand operand : instruction.operands)
                    if (operand instanceof IRVariableOperand) {
                        IRVariableOperand variableOperand = (IRVariableOperand) operand;
                        vars.remove(variableOperand.getName());
                    }
            if (!vars.isEmpty())
                System.out.println(function.name + ": " + String.join(", ", vars));
        }
        System.out.println();
    }

    public void instruction_selector(IRFunction function, MIPSProgram mips_program) {
        /*
        we want to go through each function and individually add to the predefined program
            keep adding to the program's "instructions" list until we have done all the functions
        REMEMBER:
            - for CALL and CALLR we care about calling convention but for everything else it does not matter
            - for ASSIGN (with arrays (3 args)) we care about allocating space on the stack for the array
        --> APPROACH these with caution and care
        */
        int frame_size = find_frame_size(function); // this gives us the frame size for the function

        // now with the frame size let's allocate the stack frame for this function
        Register sp = new Register("$sp", false);
        Register ra = new Register("$ra", false);
        Register fp = new Register("$fp", false); // dp we need this????

        // now let's allocate our frame on the stack
        MIPSInstruction stack_allocate = new MIPSInstruction(MIPSOp.ADDI, null, sp, sp, new Imm("-" + frame_size, "DEC"));
        mips_program.instructions.put(curr_line_num, stack_allocate);
        curr_line_num++;

        // save the return address into ra
        //NOTE: frame_size -4 is offset for return address (we are growing downward)
        MIPSInstruction store_ret_addr = new MIPSInstruction(MIPSOp.SW, null, ra, new Addr(new Imm("" + (frame_size-4), "DEC"), sp));
        mips_program.instructions.put(curr_line_num, store_ret_addr);
        curr_line_num++;

        // now save the frame pointer onto the stack
        /* 1) save the old frame pointer
         * 2) save new frame pointer
         */
        // this is to save the old frame pointer
        //NOTE: frame_size - 8 is offset for frame pointer
        MIPSInstruction store_frame_ptr = new MIPSInstruction(MIPSOp.SW, null, fp, new Addr(new Imm("" + (frame_size-8), "DEC"), sp));
        mips_program.instructions.put(curr_line_num, store_frame_ptr);
        curr_line_num++;


        /* THIS IS WRONG BECAUSE WE WANT OUR $FP to be $SP when our function executes


        // let's now set our frame pointer for our function ("bottom" of the stack) --> pointing to saved $ra
        MIPSInstruction set_frame_ptr = new MIPSInstruction(MIPSOp.ADDI, null, fp, sp, new Imm("" + frame_size, "DEC"));
        mips_program.instructions.put(curr_line_num, set_frame_ptr);
        curr_line_num++;
        */ // SO INSTEAD...........

        MIPSInstruction set_frame_ptr = new MIPSInstruction(MIPSOp.MOVE, null, fp, sp);
        mips_program.instructions.put(curr_line_num, set_frame_ptr);
        curr_line_num++;



        // now we need to store the local vars and arguments onto the stack


        
        int offset = -8;
        for (IRVariableOperand var : function.variables) {
            // WHAT THE FUCK DO WE IMPLEMENT HERE??????????????????????????//
        }



        //always save + 2 for the registers (just in case even tho we do not use them in our project) ==> WE DID NOT DO THIS YET BECAUSE WHAT????

        // now let's allocate the stack frame

        for (IRInstruction instruc : function.instructions) {
            // we want to calculate the frame size for each function
            /* process:
             *  - calc. the size of local vars
             *  - see if it is non leaf or leaf
             *  - determine number of args passed ==> size of args section
             *  - for saved registers we will assume 0 for now
             *  - add local + arg section
             *  - make sure that the frame is aligned
             */
            // For each instruction we want to translate
            if (instruc.opCode == OpCode.LABEL) {
                String label_name = ((IRLabelOperand) instruc.operands[0]).getName();
                mips_program.labels.put(label_name, curr_line_num);
                MIPSInstruction label_instruc = new MIPSInstruction(MIPSOp.LABEL, label_name);
                mips_program.instructions.put(curr_line_num, label_instruc);
                curr_line_num++;
            } else {
                translate_ir_mips(instruc, mips_program, function, frame_size);
            }
        }
    }

    public static int find_frame_size(IRFunction function) {
        // find space for the local vars
        int total_size = 0;
        for (IRVariableOperand var : function.variables) {
            if (var.type instanceof IRIntType) {
                total_size+=4;
            } else if (var.type instanceof IRArrayType) {
                // we want to add the arrays size to it
                // if int type in array then
                total_size+=((IRArrayType) var.type).getSize()*4; // we know we are only working with integers here
            }
        }
        // find space for the arguments
        int num_args = 0;
            // if true: NO NEED
            // if false: NEED SPACE !!!!!
        for (IRInstruction instruc : function.instructions) {
            if (instruc.opCode == IRInstruction.OpCode.CALL) { // it IS a non-leaf instruc
                num_args = instruc.operands.length - 1;
            } else if (instruc.opCode == IRInstruction.OpCode.CALLR) {
                num_args = instruc.operands.length - 2; // because now we have a return value too
            }
        }
        //int save_return_addr;
        int arg_size = num_args*4;
        total_size+=arg_size;
        total_size+=8; // this is for the return address and the frame pointer (4 bytes each)

        return total_size; // this is to make sure the frame is aligned
    }

    public void translate_ir_mips(IRInstruction instruc, MIPSProgram mips_program, IRFunction function, int frame_size) {
        MIPSInstruction translated_instruc;
        switch (instruc.opCode) {
            // this can be either array related or just assigning a value
            case ASSIGN:
                if (instruc.operands.length == 2) {
                    // then we have a regular assign
                    if (instruc.operands[1] instanceof IRConstantOperand) {
                        String value = ((IRConstantOperand) instruc.operands[2]).toString();
                        String type;
                        if (value.startsWith("0x")) {
                            type = "HEX";
                        } else {
                            type = "DEC";
                        }
                        translated_instruc = new MIPSInstruction(MIPSOp.LI, null, new Register(instruc.operands[0].toString()), new Imm(value, type));
                        mips_program.instructions.put(curr_line_num, translated_instruc);
                    } else if (instruc.operands[1] instanceof IRVariableOperand) {
                        translated_instruc = new MIPSInstruction(MIPSOp.MOVE, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()));
                        mips_program.instructions.put(curr_line_num, translated_instruc);
                    }
                } else {
                    // we have an array !!! SPECIAL CASE !!!!!!!
                    /* 
                     op, x , size, value
                     i.e. if ASSIGN, X, 100, 10:
                        ==> CODE:
                                type ArrayInt = array[100] of int;
                                var X : ArrayInt := 10;
                            10 is the value we assign to all elements of array X
                            and we have 100 elements
                        op, x, size, value
                            x: variable that will hold the array
                            size: # of elements the array has
                            value: the value for each element of the array when initialized
                     */
                }
                curr_line_num++;
                break;
            //these are all arithmetic operations
            /* for add, and, or ==> check if any constant operands if so ==> ADDI, ANDI, ORI 
             * EDIT: NOTE THAT according to Tiger-IR manual... FIRST OPERAND MUST BE A VARIABLE --> so if constant, MUST be operand 2 !!!!!!
            */
            case AND:
                if (instruc.operands[2] instanceof IRConstantOperand) {
                    String value = ((IRConstantOperand) instruc.operands[2]).toString();
                    String type;
                    if (value.startsWith("0x")) {
                        type = "HEX";
                    } else {
                        type = "DEC";
                    }
                    translated_instruc = new MIPSInstruction(MIPSOp.ANDI, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()), new Imm(value, type));
                    mips_program.instructions.put(curr_line_num, translated_instruc);
                } else {
                    translated_instruc = new MIPSInstruction(MIPSOp.AND, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()), new Register(instruc.operands[2].toString()));
                    mips_program.instructions.put(curr_line_num, translated_instruc);
                }
                curr_line_num++;
                break;
            case OR:
                if (instruc.operands[2] instanceof IRConstantOperand) {
                    String value = ((IRConstantOperand) instruc.operands[2]).toString();
                    String type;
                    if (value.startsWith("0x")) {
                        type = "HEX";
                    } else {
                        type = "DEC";
                    }
                    translated_instruc = new MIPSInstruction(MIPSOp.ORI, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()), new Imm(value, type));
                    mips_program.instructions.put(curr_line_num, translated_instruc);
                } else {
                    translated_instruc = new MIPSInstruction(MIPSOp.OR, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()), new Register(instruc.operands[2].toString()));
                    mips_program.instructions.put(curr_line_num, translated_instruc);
                }
                curr_line_num++;
                break;
            case ADD:
                if (instruc.operands[2] instanceof IRConstantOperand) {
                    String value = ((IRConstantOperand) instruc.operands[2]).toString();
                    String type;
                    if (value.startsWith("0x")) {
                        type = "HEX";
                    } else {
                        type = "DEC";
                    }
                    translated_instruc = new MIPSInstruction(MIPSOp.ADDI, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()), new Imm(value, type));
                    mips_program.instructions.put(curr_line_num, translated_instruc);
                } else {
                    translated_instruc = new MIPSInstruction(MIPSOp.ADD, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()), new Register(instruc.operands[2].toString()));
                    mips_program.instructions.put(curr_line_num, translated_instruc);
                }
                curr_line_num++;
                break;
            case SUB:
                translated_instruc = new MIPSInstruction(MIPSOp.SUB, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()), new Register(instruc.operands[2].toString()));
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;
                break;
            case MULT:
                translated_instruc = new MIPSInstruction(MIPSOp.MUL, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()), new Register(instruc.operands[2].toString()));
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;
                break;
            case DIV:
                translated_instruc = new MIPSInstruction(MIPSOp.DIV, null, new Register(instruc.operands[0].toString()), new Register(instruc.operands[1].toString()), new Register(instruc.operands[2].toString()));
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;
                break;
            // these are all array operations
            // for array indexing, we may care about SLL because we want to access (index * size of types stored)
                // i.e. ==> arr[1] = arr[1*sizeof(int)] or something like that
            // here we use t0 as temporary register

            // this is ARRAY_STORE: op , x, array_name, offset
                // operand[0] = x (value), operand[1] = array_base_addr, operand[2] = offset

            case ARRAY_STORE:
                Register value_as = new Register(instruc.operands[0].toString());
                Register base_addr_as = new Register(instruc.operands[1].toString());
                Register offset_as = new Register(instruc.operands[2].toString());
                Register t0_as = new Register("$t0", false);

                translated_instruc = new MIPSInstruction(MIPSOp.SLL, null, t0_as, offset_as, new Imm("2", "DEC")); // this is to account for the size of data
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;

                MIPSInstruction add_as = new MIPSInstruction(MIPSOp.ADD, null, t0_as, base_addr_as, t0_as);
                mips_program.instructions.put(curr_line_num, add_as);
                curr_line_num++;

                //Addr addr_from_as = new Addr(new Imm("0", "DEC"), t0_as);
                MIPSInstruction sw_instruc_as = new MIPSInstruction(MIPSOp.SW, null, value_as, new Addr(new Imm("0", "DEC"), t0_as));//, addr_from_as);//addr_from_as, t0_as);
                mips_program.instructions.put(curr_line_num, sw_instruc_as);
                curr_line_num++;
                break;
            //this is ARRAY_LOAD: op, x, array_base, offset
                // operand[0] = x (value) ==> we are setting this variable to the following, operand[1] = array_base, operand[2] = offset (i.e. index)
            case ARRAY_LOAD:
                Register destination_al = new Register(instruc.operands[0].toString());
                Register base_addr_al = new Register(instruc.operands[1].toString());
                Register offset_al = new Register(instruc.operands[2].toString());
                Register t0_al = new Register("$t0", false);

                translated_instruc = new MIPSInstruction(MIPSOp.SLL, null, t0_al, offset_al, new Imm("2", "DEC")); // this is to account for the size of data
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;

                MIPSInstruction add_al = new MIPSInstruction(MIPSOp.ADD, null, t0_al, base_addr_al, t0_al);
                mips_program.instructions.put(curr_line_num, add_al);
                curr_line_num++;

                MIPSInstruction load_al = new MIPSInstruction(MIPSOp.LW, null, destination_al, new Addr(new Imm("0", "DEC"), t0_al));
                mips_program.instructions.put(curr_line_num, load_al);
                curr_line_num++;
                break;
            // these are all control flow operations
            case GOTO:
                // J, JAL, JR
                String label_name = ((IRLabelOperand) instruc.operands[0]).getName();
                MIPSInstruction jump_to_label = new MIPSInstruction(MIPSOp.J, null, new Addr(label_name));
                mips_program.instructions.put(curr_line_num, jump_to_label);
                curr_line_num++;
                break;
            case CALL:
                break;
            case CALLR:
            /* after the JAL then get this value placed into v0 into the register provided */
                break;
            case RETURN:
                /* if has a return:
                    - popping from stack (second part of calling convention)
                    - get the return address
                    - jump to the return address
                    - assuming saved into stack (i.e. from JAL --> in Ra)
                    - store return value into v0
                if the last instruction is not a return and we are not in main
                    --> go to the return address saved on the stack (from the caller)
                    
                if we are in main (at the end)
                    --> do a syscall to tell that exit code = 10 (???) */
                if (function.name.equals("main")) {
                    // this is the syscall used in main to "exit"
                    mips_program.instructions.put(curr_line_num, new MIPSInstruction(MIPSOp.LI, null, new Register("$v0"), new Imm("10", "DEC")));
                    curr_line_num++;
                    // make this syscall now !!!
                    mips_program.instructions.put(curr_line_num, new MIPSInstruction(MIPSOp.SYSCALL, null));
                    curr_line_num++;
                } else { // any other function
                    if (instruc.operands.length > 0) { // place return val in $v0
                        mips_program.instructions.put(curr_line_num, new MIPSInstruction(MIPSOp.MOVE, null, new Register("$v0"), new Register(instruc.operands[0].toString())));
                        curr_line_num++;
                    }
                    // restore registers (ra is stored at frame_size - 4), (fp is stored at frame_size - 8)
                    // move fp into sp
                    MIPSInstruction move_sp = new MIPSInstruction(MIPSOp.MOVE, null, new Register("$sp"), new Register("$fp"));
                    mips_program.instructions.put(curr_line_num, move_sp);
                    curr_line_num++;

                    // get the return addrress and place into $ra
                    Imm return_offset = new Imm("" + (frame_size - 4 ), "DEC");
                    MIPSInstruction load_ret_addr = new MIPSInstruction(MIPSOp.LW, null, new Register("$ra", false), new Addr(return_offset, new Register("$sp", false)));
                    mips_program.instructions.put(curr_line_num, load_ret_addr);
                    curr_line_num++;

                    //now we want to restore the frame pointer to the previous call frame
                    Imm frame_offset = new Imm("" + (frame_size - 8), "DEC");
                    MIPSInstruction restore_fp = new MIPSInstruction(MIPSOp.LW, null, new Register("$fp"), new Addr(frame_offset, new Register("$sp"))); // prev fp
                    mips_program.instructions.put(curr_line_num, restore_fp);
                    curr_line_num++;


                    // now we want to finally reset the stack pointer to the "caller's" stack pointer before returning control flow back to it
                    Imm restore_sp = new Imm("" + (frame_size), "DEC"); // our current frame is frame_size so if we add by this amount, we will get to the "top" (bottom, since grows downwards) of the stack
                    MIPSInstruction old_sp = new MIPSInstruction(MIPSOp.ADDI, null, new Register("$sp"), new Register("$sp"), restore_sp);
                    mips_program.instructions.put(curr_line_num, old_sp);
                    curr_line_num++;


                    // now that we have restored stack values into respective registers, we can jump back to the return address we have in $ra
                    MIPSInstruction jump_to = new MIPSInstruction(MIPSOp.JR, null, new Register("$ra"));
                    mips_program.instructions.put(curr_line_num, jump_to);
                    curr_line_num++;
                }
                break;
            // these are all branches and are one-to-one corresponded
            case BREQ:
                // instruction has "op", "lable", "operands"
                translated_instruc = new MIPSInstruction(MIPSOp.BEQ, null,
                    new Register(instruc.operands[0].toString()),
                    new Register(instruc.operands[1].toString()),
                    new Addr(instruc.operands[2].toString())
                );
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;
                break;
            case BRNEQ:
                translated_instruc = new MIPSInstruction(MIPSOp.BNE, null,
                    new Register(instruc.operands[0].toString()),
                    new Register(instruc.operands[1].toString()),
                    new Addr(instruc.operands[2].toString())
                );
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;
                break;
            case BRLT:
                translated_instruc = new MIPSInstruction(MIPSOp.BLT, null,
                    new Register(instruc.operands[0].toString()),
                    new Register(instruc.operands[1].toString()),
                    new Addr(instruc.operands[2].toString())
                );
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;
                break;
            case BRGT:
                translated_instruc = new MIPSInstruction(MIPSOp.BGT, null,
                    new Register(instruc.operands[0].toString()),
                    new Register(instruc.operands[1].toString()),
                    new Addr(instruc.operands[2].toString())
                );
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;
                break;
            case BRGEQ:
                translated_instruc = new MIPSInstruction(MIPSOp.BGE, null,
                    new Register(instruc.operands[0].toString()),
                    new Register(instruc.operands[1].toString()),
                    new Addr(instruc.operands[2].toString())
                );
                mips_program.instructions.put(curr_line_num, translated_instruc);
                curr_line_num++;
                break;
            default:
                break;
        }
    }
    
    public static void calculateSets(IRcfg cfg) {
        for (IRNode node : cfg.nodes) {
            if (node.defined_var == null) { // if not a defintion skip it
                continue;
            }
            node.addToGen(node);
            node.addToOut(node); //OUT = GEN


            for (IRNode nested_node : cfg.nodes) {
                if (nested_node.defined_var == null) {
                    continue;
                }
                // if they both define the same variable AND they are not the same node
                if ((nested_node.defined_var.equals(node.defined_var)) && (!nested_node.equals(node))) {
                    node.addToKill(nested_node);
                }
            }
        }
        //after: GEN, KILL are intialized, IN = null/empty, OUT = GEN
    }

    public static void fixedPointAlg(IRcfg cfg) {
        /* Continuously traverse CFG until IN/OUT do NOT change ==> reached the Fixed Point 
            NOTE: IN[B] = OUT[P] for P in B.predecessors 
                  OUT[B] = GEN[B] U (IN[B] - KILL[B]) */
        boolean changed = true;
        while (changed) {
            changed = false;
            for (IRNode node : cfg.nodes) {
                //CALCULATE IN SET: loop through IMMEDIATE predecessor(s),find "their" OUT and "union" all of it together
                Set<IRNode> new_IN = new HashSet<>();
                for (IRNode pre_node : node.predecessors) {
                    for (IRNode out_elem : pre_node.OUT) {
                        new_IN.add(out_elem);
                    }
                }
                node.IN = new_IN;

                //Following the instructions in Lecture 3 Slide 32, lets just directly set OUT set
                Set<IRNode> new_OUT = new HashSet<>(node.GEN);
                Set<IRNode> in_minus_kill = new HashSet<>();
                for (IRNode in_node : node.IN) {
                    in_minus_kill.add(in_node);
                }
                for (IRNode kill_node : node.KILL) {
                    in_minus_kill.remove(kill_node);
                }
                for (IRNode imk_node : in_minus_kill) {
                    new_OUT.add(imk_node);
                }

                if (!node.OUT.equals(new_OUT)) {
                    changed = true;
                    node.OUT = new_OUT;
                }
            }
        }
    }

    public static void markAlg(IRcfg cfg) {
        Queue<IRNode> worklist = new LinkedList<>();
        for (IRNode node : cfg.nodes) {
            node.is_marked = false;
            switch(node.instruction.opCode) {
                case GOTO, BREQ, BRNEQ, BRLT, BRGT, BRGEQ, CALL, CALLR, RETURN, ARRAY_STORE -> {
                    node.is_marked = true;
                    worklist.add(node);
                }
                default -> {
                    break;
                }
            }
        }
        // With worklist created, let's implement part 2 of the Mark Algorithm
        IRNode worklist_node = worklist.poll();
        while (worklist_node != null) {
            List<String> used_vars = worklist_node.used_vars;
            
            for (String used_var : used_vars) {
                for (IRNode maybe_important : worklist_node.IN) {
                    if (maybe_important.defined_var.equals(used_var)) {
                        if (!maybe_important.is_marked) {
                            maybe_important.is_marked = true;
                            worklist.add(maybe_important);
                        }
                    }
                }
            }
            worklist_node = worklist.poll();
        }
    }

    public static void sweepAlg(IRcfg cfg, IRFunction func) {
        List<IRInstruction> final_instructions = new ArrayList<>();
        for (IRNode node : cfg.nodes) {
            if (node.is_marked || node.instruction.opCode == IRInstruction.OpCode.LABEL) {
                final_instructions.add(node.instruction);
            }
        }
        func.instructions = final_instructions;
    }
}