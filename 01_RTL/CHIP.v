//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
module CHIP #(                                                                                  //
    parameter BIT_W = 32                                                                        //
)(                                                                                              //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        //
        output [BIT_W-1:0]  o_IMEM_addr,                                                        //
        output              o_IMEM_cen,                                                         //
    // data memory                                                                              //
        input               i_DMEM_stall,                                                       //
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen,                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        //
        output [BIT_W-1:0]  o_DMEM_wdata,                                                       //
    // finnish procedure                                                                        //
        output              o_finish,                                                           //
    // cache                                                                                    //
        input               i_cache_finish,                                                     //
        output              o_proc_finish                                                       //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any declaration
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    parameter SINGLE = 1'b0;
    parameter MULTIPLE = 1'b1;
// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC, next_PC;
        wire mem_cen, mem_wen;
        wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
        wire mem_stall;

        wire Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
        wire [1:0] ALUOp;
        wire [BIT_W-1:0] WriteData, ReadData1, ReadData2;
        wire [BIT_W-1:0] alu_in_2;
        wire Zero;
        wire [BIT_W-1:0] ALUresult;
        wire jump; // (Branch && Zero): pc_mux_control

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment
    assign jump = Branch && Zero;
// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    Control control(.opcode(i_IMEM_data[6:0]), .Branch(Branch), .MemRead(.MemRead), .MemtoReg(MemtoReg), .ALUOp(ALUOp), .MemWrite(MemWrite), .ALUSrc(ALUSrc), .RegWrite(RegWrite));
    Immediate_gen imm_gen(.instruction(i_IMEM_data), .imm_addr(imm_addr));
    Mux mux_reg_alu(.control(ALUSrc), .izero(ReadData2), ione(imm_addr), .out(alu_in_2));
    memory mem(.i_clk(i_clk), .i_rst_n(i_rst_n), .i_cen, .i_wen,
               .i_addr, .i_wdata, .o_rdata, .o_stall, .i_offset, .i_ubound, .i_cache);

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (RegWrite),          
        .rs1    (i_IMEM_data[19:15]),                
        .rs2    (i_IMEM_data[24:20]),                
        .rd     (i_IMEM_data[11:7]),                 
        .wdata  (WriteData),             
        .rdata1 (ReadData1),           
        .rdata2 (ReadData2)
    );

     basic_alu ALU(
        // input
        .i_clk(i_clk),
        .i_rst_n(i_rst_n), 
        .in_A(ReadData1),
        .in_B(alu_in_2),
        .AluControl(AluControl),
        // output
        .out(ALUresult),
        .zero(Zero)
    );


// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
        end
        else begin
            PC <= next_PC;
        end
    end
endmodule

module Mux #(parameter BIT_W = 32)(
    input control,
    input [BIT_W-1:0] izero, ione,
    input [BIT_W-1:0] out
);
    assign out = (control)? ione: izero;
endmodule

module Control(
    input [6:0] opcode,
    output Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite,
    output [1:0] ALUOp
);
    always @(*) begin
        case (opcode[6:2])
            // R-type: add, sub, and, xor
            5'b01100: begin 
                ALUSrc = 1'b0;
                RegWrite = 1'b1;
                MemRead = 1'b0;
                MemWrite = 1'b0;
                MemtoReg = 1'b0;
                Branch = 1'b0;
                ALUOp = 2'b10; 
                Jal = 1'b0;
                Jalr = 1'b0;
            end
            // I-type: lw
            5'b00000: begin 
                ALUSrc = 1'b1;
                RegWrite = 1'b1;
                MemRead = 1'b1;
                MemWrite = 1'b0;
                MemtoReg = 1'b1;
                Branch = 1'b0;
                ALUOp = 2'b00; // add
                Jal = 1'b0;
                Jalr = 1'b0;
            end
            5'b00100: begin // I-type: immediate
            // addi: add
            // slti: sub
                ALUSrc = 1'b1;
                RegWrite = 1'b1;
                MemRead = 1'b0;
                MemWrite = 1'b0;
                MemtoReg = 1'b0;
                Branch = 1'b0;
                ALUOp = 2'b10; // to be determined by func3 & func7
                Jal = 1'b0;
                Jalr = 1'b0;
            end
            5'b11001: begin // I-type: jalr
            // jalr: add
                ALUSrc = 1'b1;
                RegWrite = 1'b1;
                MemRead = 1'b0;
                MemWrite = 1'b0;
                MemtoReg = 1'b0;
                Branch = 1'b0;
                ALUOp = 2'b00;
                Jal = 1'b0;
                Jalr = 1'b1;
            end
            5'b01000: begin // S-type
                ALUSrc = 1'b1;
                RegWrite = 1'b0;
                MemRead = 1'b0;
                MemWrite = 1'b1;
                MemtoReg = 1'b0;
                Branch = 1'b0;
                ALUOp = 2'b00; // add
                Jal = 1'b0;
                Jalr = 1'b0;
            end
            5'b11000: begin // B-type
                ALUSrc = 1'b0;
                RegWrite = 1'b0;
                MemRead = 1'b0;
                MemWrite = 1'b0;
                MemtoReg = 1'b0;
                Branch = 1'b1;
                ALUOp = 2'b01; // sub
                Jal = 1'b0;
                Jalr = 1'b0;
            end
            5'b11011: begin // J-type: jal
                ALUSrc = 1'b1;
                RegWrite = 1'b1;
                MemRead = 1'b0;
                MemWrite = 1'b0;
                MemtoReg = 1'b0;
                Branch = 1'b0;
                ALUOp = 2'b00; // add
                Jal = 1'b1;
                Jalr = 1'b0;
            end
            5'b00101: begin // U-type: auipc
                ALUSrc = 1'b1;
                RegWrite = 1'b1;
                MemRead = 1'b0;
                MemWrite = 1'b0;
                MemtoReg = 1'b0;
                Branch = 1'b0;
                ALUOp = 2'b00;
                Jal = 1'b0;
                Jalr = 1'b0;
            end
            default: begin
                ALUSrc = 1'b0;
                RegWrite = 1'b0;
                MemRead = 1'b0;
                MemWrite = 1'b0;
                MemtoReg = 1'b0;
                Branch = 1'b0;
                ALUOp = 2'b00;
                Jal = 1'b0;
                Jalr = 1'b0;                
            end
        endcase
    end
endmodule

module Immediate_gen #(parameter BIT_W = 32)(
    input  [BIT_W-1:0] instruction;
    output [BIT_W-1:0] imm_addr;
);
    always@(*) begin
        case(instruction[6:0])
        7'b0110011: // R-type: add, sub, and, xor
            imm_addr = {(BIT_W){1'b0}};
        7'b0010011: // I-type: addi, slli, slti, srai
            begin
                if(instruction[14:12]==3'b001 || instruction[14:12]==3'b101) // slli, srai
                    imm_addr = {{(BIT_W-5){instruction[24]}},instruction[24:20]};
                else if(instruction[14:12]==3'b000 || instruction[14:12]==3'b010) // addi, slti
                    imm_addr = {{(BIT_W-12){instruction[31]}},instruction[31:20]};
            end
        7'b0000011: // I-type: lw
            imm_addr = {{(BIT_W-12){instruction[31]}},instruction[31:20]};
        7'b1100111: // I-type: jalr
            imm_addr = {{(BIT_W-12){instruction[31]}},instruction[31:20]};
        7'b0100011: // S-type: sw 
            imm_addr = {{(BIT_W-12){instruction[31]}},instruction[31:25],instruction[11:7]};
        7'b1100011: // B-type: beq, bge, blt, bne
            imm_addr = {{(BIT_W-12){instruction[31]}},instruction[31],instruction[7],instruction[30:25],instruction[11:8]};
        7'b1101111: // J-type: jal 
            imm_addr = {{(BIT_W-20){instruction[31]}},instruction[31],instruction[19:12],instruction[20],instruction[30:21]};
        7'b0010111: // U-type: auipc
            imm_addr ={instruction[31:12],12'b0};
        default:   
            imm_addr = {(BIT_W){1'b0}};
        endcase
    end    

endmodule

module Alu_control(
    input [6:0] opcode,
    input [1:0] ALUOp, 
    input [2:0] func3,
    input instruction_30;
    output [3:0] AluControl
);
    reg [3:0] alu_control;

    always @(*) begin
        case(ALUOp)
            2'b00: alu_control = 4'b0010; // add
            2'b01: alu_control = 4'b0110; // subtract
            2'b10: begin
                case(instruction_30)
                    1'b0: begin
                        case(func3) 
                            3'b000: alu_control = 4'b0010; // add
                            3'b111: alu_control = 4'b0000; // and
                            3'b110: alu_control = 4'b0001; // or
                        endcase
                    end
                    1'b1: alu_control = 4'b0110; // subtract
                endcase                
            end
            default: alu_control = 4'b0000;
        endcase        
    end

    assign AluControl = alu_control;
endmodule

module Shift_left_1#(parameter BIT_W = 32)(
    input [BIT_W-1:0] imm_addr,
    output [BIT_W-1:0] imm_offset
);

assign imm_offset = imm_addr << 1;
endmodule

module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule
module basic_alu(
    // input
    clk,
    in_A,
    in_B,
    AluControl,
    // output
    out,
    zero
);
    input clk;
    input [31:0] in_A, in_B;
    input [3:0] AluControl;

    output reg [31:0] out;
    output reg zero;

    always@(*)begin
        case(AluControl)
        4'b0000:    //AND
        begin
            out = in_A & in_B;
            zero = 1'b0;
        end
        4'b0010:    //ADD
        begin
            out = in_A + in_B;
            zero = 1'b0;
        end
        4'b0011:    //SLLI
        begin
            out = in_A << in_B;
            zero = 1'b0;
        end
        4'b0100:    //SLTI
        begin
            out = ((~in_A+1) < (~in_B+1))?1'b1:1'b0;
            zero = 1'b0;
            end
        4'b0101:    //SRAI
        begin
            out = in_A >>> in_B;
        end
        4'b0110:    //SUBTRACT
        begin
            out = in_A - in_B;
            zero = (out == 32'b0)?1'b1:1'b0;
        end
        4'b1110:    //SUBTRACT bne
        begin
            out = in_A - in_B;
            zero = (out == 32'b0)?1'b0:1'b1;
        end
        4'b0111:    //SLT
        begin
            out = (in_A < in_B)?32'b1:32'b0;
            zero = 1'b0;
        end
        4'b1100:    //XOR
        begin
            out = in_A ^ in_B;
            zero = 1'b0;
        end
        default:
        begin
            out =64'b0;
            zero = 1'b0;
        end
        endcase
    end

endmodule

module MULDIV_unit(
    // TODO: port declaration
    );
    // Todo: HW2
endmodule

module Cache#(
        parameter BIT_W = 32,
        parameter ADDR_W = 32
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
            input i_proc_finish,
            output o_cache_finish,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W*4-1:0]  o_mem_wdata,
            input [BIT_W*4-1:0] i_mem_rdata,
            input i_mem_stall,
            output o_cache_available,
        // others
        input  [ADDR_W-1: 0] i_offset
    );

    assign o_cache_available = 0; // change this value to 1 if the cache is implemented

    //------------------------------------------//
    //          default connection              //
    assign o_mem_cen = i_proc_cen;              //
    assign o_mem_wen = i_proc_wen;              //
    assign o_mem_addr = i_proc_addr;            //
    assign o_mem_wdata = i_proc_wdata;          //
    assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    assign o_proc_stall = i_mem_stall;          //
    //------------------------------------------//

    // Todo: BONUS

endmodule
