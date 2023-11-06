`include "includes/clockworks.v"
`include "emitter_uart.v"
`include "defines.v"
`include "spi_flash.v"
//checkpoint
module Memory (
  input              clk,
  input       [31:0] mem_addr,      // Address to be read
  output reg  [31:0] mem_rdata,     // Data Read
  input              mem_rstrb,     // Goes High when the processor wants to Read
  input       [31:0] mem_wdata,     // Data to be written
  input       [3:0]  mem_wmask      // Mask for writing the 4 Bytes
  );

   reg [31:0] MEM [0:1535]; // 1536 4-bytes words = 6 Kb of RAM in total

  initial begin
      $readmemh("firmware.hex",MEM);
  end

  // `ifdef BENCH
  //   localparam slow_bit=12;
  // `else
  //   localparam slow_bit=19;
  // `endif

  // // Memory-mapped IO in IO page, 1-hot addressing in word address.
  // localparam  IO_LEDS_bit   = 0;  // write led bits
  // localparam  IO_UART_DAT_bit = 1;  // write data to send 8 bits
  // localparam  IO_UART_CNTL_bit = 2;  // Read Status

  // // Converts an IO_xxx_bit constant into an offset in IO page.
  // function [31:0] IO_BIT_TO_OFFSET;
  //   input  [31:0] bit_id;
  //   begin
  //     IO_BIT_TO_OFFSET = 1 << (bit_id + 2);
  //   end
  // endfunction


  // `include "includes/riscv_assembly.v"
  // // ******************code here**************

  //    `define mandel_shift 10
  //    `define mandel_mul (1 << `mandel_shift)
  //    `define xmin (-2*`mandel_mul)
  //    `define xmax ( 2*`mandel_mul)
  //    `define ymin (-2*`mandel_mul)
  //    `define ymax ( 2*`mandel_mul)
  //    `define dx ((`xmax-`xmin)/80)
  //    `define dy ((`ymax-`ymin)/80)
  //    `define norm_max (4 << `mandel_shift)

  //    integer    mandelstart_ = 12;
  //    integer    blink_       = 16;
  //    integer    loop_y_      = 76;
  //    integer    loop_x_      = 84;
  //    integer    loop_Z_      = 96;
  //    integer    exit_Z_      = 188;
  //    integer    wait_        = 264;
  //    integer    wait_L0_     = 272;
  //    integer    putc_        = 284;
  //    integer    putc_L0_     = 292;
  //    integer    mulsi3_      = 308;
  //    integer    mulsi3_L0_   = 316;
  //    integer    mulsi3_L1_   = 328;

  //    integer    colormap_    = 344;

  //    // X,Y         : s0,s1
  //    // Cr,Ci       : s2,s3
  //    // Zr,Zi       : s4,s5
  //    // Zrr,2Zri,Zii: s6,s7,s8
  //    // cnt: s10
  //    // 128: s11

  //    initial begin
  //       LI(sp,32'h1800);   // End of RAM, 6kB
  //       LI(gp,32'h400000); // IO page

  //    Label(mandelstart_);

  //       // Blink 5 times.
  //       LI(s0,5);
  //    Label(blink_);
  //       LI(a0,5);
  //       SW(a0,gp,IO_BIT_TO_OFFSET(IO_LEDS_bit));
  //       CALL(LabelRef(wait_));
  //       LI(a0,10);
  //       SW(a0,gp,IO_BIT_TO_OFFSET(IO_LEDS_bit));
  //       CALL(LabelRef(wait_));
  //       ADDI(s0,s0,-1);
  //       BNEZ(s0,LabelRef(blink_));
  //       LI(a0,0);
  //       SW(a0,gp,IO_BIT_TO_OFFSET(IO_LEDS_bit));


  //       LI(s1,0);
  //       LI(s3,`xmin);
  //       LI(s11,80);

  //    Label(loop_y_);
  //       LI(s0,0);
  //       LI(s2,`ymin);

  //    Label(loop_x_);
  //       MV(s4,s2); // Z <- C
  //       MV(s5,s3);

  //       LI(s10,9); // iter <- 9

  //    Label(loop_Z_);
  //       MV(a0,s4); // Zrr  <- (Zr*Zr) >> mandel_shift
  //       MV(a1,s4);
  //       CALL(LabelRef(mulsi3_));
  //       SRLI(s6,a0,`mandel_shift);
  //       MV(a0,s4); // Zri <- (Zr*Zi) >> (mandel_shift-1)
  //       MV(a1,s5);
  //       CALL(LabelRef(mulsi3_));
  //       SRAI(s7,a0,`mandel_shift-1);
  //       MV(a0,s5); // Zii <- (Zi*Zi) >> (mandel_shift)
  //       MV(a1,s5);
  //       CALL(LabelRef(mulsi3_));
  //       SRLI(s8,a0,`mandel_shift);
  //       SUB(s4,s6,s8); // Zr <- Zrr - Zii + Cr
  //       ADD(s4,s4,s2);
  //       ADD(s5,s7,s3); // Zi <- 2Zri + Cr

  //       ADD(s6,s6,s8); // if norm > norm max, exit loop
  //       LI(s7,`norm_max);
  //       BGT(s6,s7,LabelRef(exit_Z_));

  //       ADDI(s10,s10,-1);  // iter--, loop if non-zero
  //       BNEZ(s10,LabelRef(loop_Z_));

  //    Label(exit_Z_);
  //       LI(a0,colormap_);
  //       ADD(a0,a0,s10);
  //       LBU(a0,a0,0);
  //       CALL(LabelRef(putc_));

  //       ADDI(s0,s0,1);
  //       ADDI(s2,s2,`dx);
  //       BNE(s0,s11,LabelRef(loop_x_));

  //       LI(a0," ");
  //       CALL(LabelRef(putc_));
  //       LI(a0,"\n");
  //       CALL(LabelRef(putc_));

  //       ADDI(s1,s1,1);
  //       ADDI(s3,s3,`dy);
  //       BNE(s1,s11,LabelRef(loop_y_));


  //       J(LabelRef(mandelstart_));

  //       EBREAK(); // I systematically keep it before functions
  //                 // in case I decide to remove the loop...

  //    Label(wait_);
  //       LI(t0,1);
  //       SLLI(t0,t0,slow_bit);
  //    Label(wait_L0_);
  //       ADDI(t0,t0,-1);
  //       BNEZ(t0,LabelRef(wait_L0_));
  //       RET();

  //    Label(putc_);
  //       // Send character to UART
  //       SW(a0,gp,IO_BIT_TO_OFFSET(IO_UART_DAT_bit));
  //       // Read UART status, and loop until bit 9 (busy sending)
  //       // is zero.
  //       LI(t0,1<<9);
  //    Label(putc_L0_);
  //       LW(t1,gp,IO_BIT_TO_OFFSET(IO_UART_CNTL_bit));
  //       AND(t1,t1,t0);
  //       BNEZ(t1,LabelRef(putc_L0_));
  //       RET();

  //       // Mutiplication routine,
  //       // Input in a0 and a1
  //       // Result in a0
  //    Label(mulsi3_);
  //       MV(a2,a0);
  //       LI(a0,0);
  //    Label(mulsi3_L0_);
  //       ANDI(a3,a1,1);
  //       BEQZ(a3,LabelRef(mulsi3_L1_));
  //       ADD(a0,a0,a2);
  //    Label(mulsi3_L1_);
  //       SRLI(a1,a1,1);
  //       SLLI(a2,a2,1);
  //       BNEZ(a1,LabelRef(mulsi3_L0_));
  //       RET();

  //    Label(colormap_);
  //       DATAB(" ",".",",",":");
  //       DATAB(";","o","x","%");
  //       DATAB("#","@", 0 , 0 );
  //       endASM();
  // end
  // // *****************************************

  wire [29:0] word_addr = mem_addr[31:2];

  always @ ( posedge clk ) begin
    if (mem_rstrb) begin
      mem_rdata <= MEM[word_addr];
    end

  if (mem_wmask[0]) MEM[word_addr][ 7:0 ] <= mem_wdata [ 7:0 ];
  if (mem_wmask[1]) MEM[word_addr][15:8 ] <= mem_wdata [15:8 ];
  if (mem_wmask[2]) MEM[word_addr][23:16] <= mem_wdata [23:16];
  if (mem_wmask[3]) MEM[word_addr][31:24] <= mem_wdata [31:24];

  end
endmodule // memory

module Processor (
  input             clk,
  input             resetn,
  input      [31:0] mem_rdata,
  output     [31:0] mem_addr,
  output            mem_rstrb,
  output     [ 3:0] mem_wmask,
  output     [31:0] mem_wdata,
  input         mem_rbusy
);

  reg [31:0] pc = 0;
  reg [31:0] instr;
   
  // RV32 Base opcode defination
  wire is_LOAD    =  (instr[6:0] == 7'b0000011); // rd <- mem[src1_value+Iimm]
  wire is_STORE   =  (instr[6:0] == 7'b0100011); // mem[src1_value+Simm] <- src2_value
  wire is_BRANCH  =  (instr[6:0] == 7'b1100011); // if(src1_value OP src2_value) pc<-pc+Bimm
  wire is_JALR    =  (instr[6:0] == 7'b1100111); // rd <- pc+4; pc<-src1_value+Iimm
  wire is_FENCE   =  (instr[6:0] == 7'b0001111);
  wire is_JAL     =  (instr[6:0] == 7'b1101111); // rd <- pc+4; pc<-pc+Jimm
  wire is_OPIM    =  (instr[6:0] == 7'b0010011); // rd <- src1_value OP Iimm
  wire is_OP      =  (instr[6:0] == 7'b0110011); // rd <- src1_value OP src2_value
  wire is_SYSTEM  =  (instr[6:0] == 7'b1110011); // special
  wire is_AUIPC   =  (instr[6:0] == 7'b0010111); // rd <- pc + Uimm
  wire is_LUI     =  (instr[6:0] == 7'b0110111); // rd <- Uimm

   // The 5 immediate formats
  wire [31:0] I_imm = {{21{instr[31]}}, instr[30:20]  };
  wire [31:0] S_imm = {{21{instr[31]}}, instr[30:25], instr[11:7] };
  wire [31:0] B_imm = {{20{instr[31]}}, instr[7],     instr[30:25] , instr[11:8],1'b0};
  wire [31:0] U_imm = {    instr[31],   instr[30:12], {12{1'b0}}  };
  wire [31:0] J_imm = {{12{instr[31]}}, instr[19:12], instr[20]    , instr[30:21],1'b0};
   
  // immdiate validity
  wire is_i_instr = is_LOAD || is_OPIM || is_JALR;
  wire is_u_instr = is_LUI || is_AUIPC ;
  wire is_s_instr = is_STORE ;
  wire is_b_instr = is_BRANCH ;
  wire is_j_instr = is_JAL;

  wire [31:0] imm  = is_i_instr ? {{21{instr[31]}}, instr[30:20]  }:
                     is_s_instr ? {{21{instr[31]}}, instr[30:25], instr[11:7] }:
                     is_b_instr ? {{20{instr[31]}}, instr[7],     instr[30:25] , instr[11:8],1'b0}:
                     is_u_instr ? {    instr[31],   instr[30:12], {12{1'b0}}  }:
                     is_j_instr ? {{12{instr[31]}}, instr[19:12], instr[20]    , instr[30:21],1'b0}:
                     32'b0;

     // instruction fields
  wire [4:0] rs1 = instr[19:15];
  wire [4:0] rs2 = instr[24:20];
  wire [4:0] rd  = instr[11:7];
  wire [2:0] funct3 = instr[14:12];
   wire [6:0] funct7 = instr[31:25];
  wire [6:0] opcode = instr[6:0];

  wire [10:0] dec_bits = {instr[30],funct3,opcode};
   
   // The registers bank
   reg [31:0] register_bank [0:31];

  // Initialize registers to 0
`ifdef BENCH   
     integer i;
   initial begin
      for(i=0; i<32; ++i) begin
	 register_bank[i] = 0;
      end
   end
`endif   

  // registers
  reg [31:0] src1_value;
  reg [31:0] src2_value;

  // ALU
  // ALU Registers
  reg  [31:0] alu_out;
  wire [31:0] alu_in1 = src1_value;
  wire [31:0] alu_in2 = is_OP | is_BRANCH ? src2_value : imm;  //imm
  wire [ 4:0] shamt   = is_OP ? src2_value[4:0] : instr[24:20];

  // Adder
   wire [31:0] alu_plus = alu_in1 + alu_in2;
  // 33 Bit subtractor
   wire [32:0] alu_minus = {1'b1, ~alu_in2} + {1'b0,alu_in1} + 33'b1;
  //comparator using subtractor
  wire lt  = (alu_in1[31] ^ alu_in2[31]) ? alu_in1[31] : alu_minus[32];
  wire ltu = alu_minus[32];
  wire eq  = (alu_minus[31:0] == 0);

  always @ ( * ) begin
      case(funct3)
      `f3_add  : alu_out = (funct7[5] & instr[5]) ? alu_minus[31:0] : alu_plus;
      `f3_sll  : alu_out = alu_in1 << shamt;
      `f3_slt  : alu_out = {31'b0, lt};
      `f3_sltu : alu_out = {31'b0, ltu};
      `f3_xor  : alu_out = (alu_in1 ^ alu_in2);
      `f3_sr   : alu_out = funct7[5]? ($signed(alu_in1) >>> shamt) : ($signed(alu_in1) >> shamt);
      `f3_or   : alu_out = (alu_in1 | alu_in2);
      `f3_and  : alu_out = (alu_in1 & alu_in2);
      endcase
   end

  // Brach machine
   reg take_branch;

  always @ ( * ) begin
      case(funct3)
      `f3_beq   : take_branch = eq;
      `f3_bne   : take_branch = !eq;
      `f3_blt   : take_branch = lt;
      `f3_bge   : take_branch = !lt;
      `f3_bltu  : take_branch = ltu;
      `f3_bgeu  : take_branch = !ltu;
      default   : take_branch = 1'b0;
      endcase
   end
   
  // Next pc
  wire [31:0] pc_plus_imm = pc + imm;
   
  wire [31:0] pc_plus_4   = pc + 32'd4;
   
  wire[31:0] next_pc = (is_BRANCH && take_branch) ? pc_plus_imm :
                       is_JAL                     ? pc_plus_imm :
                       is_JALR                    ? {alu_plus[31:1],1'b0} :
                       pc_plus_4
  ;
                                               
  // Register write back
  wire [31:0] writeback_data;
  wire        writeback_en;

  assign writeback_data = (is_JAL ||is_JALR) ? (pc_plus_4)   :
                          is_LUI             ? imm           :
                          is_AUIPC           ? pc_plus_imm   :
                          is_LOAD            ? load_data     :
                          alu_out
  ;

  wire [31:0] loadstore_addr = src1_value + imm;

  wire mem_byte_access      = funct3[1:0] == 2'b00;
  wire mem_halfword_access  = funct3[1:0] == 2'b01;

   wire [15:0] load_halfword = loadstore_addr[1] ? mem_rdata[31:16] : mem_rdata[15:0];
  wire [7:0]  load_byte     = loadstore_addr[0] ? load_halfword[15:8] : load_halfword[7:0];

   wire load_sign = !funct3[2] & (mem_byte_access ? load_byte[7] : load_halfword[15]);

  wire [31:0] load_data = mem_byte_access     ? {{24{load_sign}}  ,   load_byte} :
     mem_halfword_access ? {{16{load_sign}}, load_halfword} :
                          mem_rdata 
                          ;
   
   // Store
  // 31 : 24 | 23 : 16 | 15 : 8 | 7 : 0

    //                              [7:0]   byte 00
  //                      [7:0]           byte 01
  //            [7:0]                     byte 10
  //  [7:0]                               byte 11

  //                     [15:8]  [7:0]    hw   00
  //  [15:8]    [7:0]                     hw   10

  //  [31:26]  [23:16]  [15:8]  [7:0]     w    00
  
  assign mem_wdata[ 7:0 ] = src2_value[7:0];
  assign mem_wdata[15:8 ] = loadstore_addr[0] ? src2_value[ 7:0] : src2_value[15:8 ];
  assign mem_wdata[23:16] = loadstore_addr[1] ? src2_value[ 7:0] : src2_value[23:16];
  assign mem_wdata[31:24] = loadstore_addr[0] ? src2_value[ 7:0] :
                            loadstore_addr[1] ? src2_value[15:8] : src2_value[31:24]
  ;

   wire [3:0] store_mask =
    (mem_byte_access) ?
	            (loadstore_addr[1]   ?
        (loadstore_addr[0] ? 4'b1000 : 4'b0100) :   // 11  10
        (loadstore_addr[0] ? 4'b0010 : 4'b0001)     // 01  00
        ):
	      mem_halfword_access  ?
        (loadstore_addr[1] ? 4'b1100 : 4'b0011) :   // 10 00
              4'b1111
              ;
   
  // State machine
   localparam  fetch_instr = 0;
   localparam  wait_instr  = 1;
   localparam  execute     = 2;
   localparam  wait_data   = 3;
   reg [1:0] state = fetch_instr;
   
   always @(posedge clk) begin
    //  Reset
      if(resetn) begin
      pc <= 0;
	 state <= fetch_instr;
      end 

      else begin
	 if(writeback_en && rd != 0) 
   begin
	    register_bank[rd] <= writeback_data;
	 end

	 case(state)
	   fetch_instr: begin
	      state <= wait_instr;
	   end

	   wait_instr: begin
	      instr[31:2] <= mem_rdata[31:2];
	      src1_value <= register_bank[mem_rdata[19:15]];
	      src2_value <= register_bank[mem_rdata[24:20]];
	      state <= execute;
	   end

	   execute: begin
          if (!is_SYSTEM) begin
		 pc <= next_pc;
	      end
	      state <= is_LOAD  ? wait_data : fetch_instr;

`ifdef BENCH      
	      if(is_SYSTEM) $finish();
`endif      
	   end

	    wait_data: begin
	      if(!mem_rbusy) begin
		 state <= fetch_instr;
	      end
	   end

	 endcase 
      end
   end

   assign writeback_en = (state == execute && !is_BRANCH && !is_STORE) || (state == wait_data);
   assign mem_addr  = (state == wait_instr  || state == fetch_instr) ? pc :loadstore_addr ;
   assign mem_rstrb = (state == fetch_instr || (state == execute & is_LOAD));
   assign mem_wmask = {4{(state == execute) & is_STORE}} & store_mask;

  // BENCH TEST CODE
  // `ifdef BENCH
  //   always @(*)
  //     if(state == fetch_reg) begin
  //       $display("");
  //       $display("pc=%0d",pc);
  //       // $display("dec_bits=%b",dec_bits);
  //       // $display("instruction =%b\n",instr);
  //
  //       casex (dec_bits)
  //         `is_lui   : $write("lUI");
  //         `is_auipc : $write("AUIPC");
  //         `is_jal   : $write("JAL");
  //         `is_jalr  : $write("JALR");
  //         `is_beq   : $write("BEQ");
  //         `is_bne   : $write("BNE");
  //         `is_blt   : $write("BLT");
  //         `is_bge   : $write("BGE");
  //         `is_bltu  : $write("BLTU");
  //         `is_bgeu  : $write("BGEU");
  //         `is_load  : $write("LOAD");
  //         `is_addi  : $write("ADDI");
  //         `is_slti  : $write("SLTI");
  //         `is_sltiu : $write("SLTIU");
  //         `is_xori  : $write("XORI");
  //         `is_ori   : $write("ORI");
  //         `is_andi  : $write("ANDI");
  //         `is_slli  : $write("SLLI");
  //         `is_srli  : $write("SRLI");
  //         `is_srai  : $write("SRAI");
  //         `is_add   : $write("ADD");
  //         `is_sub   : $write("SUB");
  //         `is_sll   : $write("SLL");
  //         `is_slt   : $write("SLT");
  //         `is_sltu  : $write("SLTU");
  //         `is_xor   : $write("XOR");
  //         `is_srl   : $write("SRL");
  //         `is_sra   : $write("SRA");
  //         `is_or    : $write("OR");
  //         `is_and   : $write("AND");
  //         `is_fence    : $write("FENCE");
  //         `is_ecall    : $write("ECALL");
  //         `is_ebreak   : $write("EBREAK");
  //       endcase
  //
  //       case (1'b1)
  //         is_OP: $display(
  //           " rd=%d rs1=%d rs2=%d ",
  //           rd, rs1, rs2 );
  //
  //         is_OPIM: $display(
  //         	" rd=%d rs1=%d imm=%0d ",
  //           rd, rs1, I_imm);
  //       endcase
  //
  //       if(is_SYSTEM) begin
  //    	    $finish();
  //    	  end
  //     end
  // `endif

endmodule //processor

module SOC (
    input               CLK,        // system clock
    input               RESET,      // reset button
    output reg [4:0]    LEDS, // system LEDs
    input               RXD,        // UART receive
    output              TXD,         // UART transmit
    output 	            SPIFLASH_CLK,  // SPI flash clock
    output 	            SPIFLASH_CS_N, // SPI flash chip select (active low)
    output              SPIFLASH_MOSI,
    input               SPIFLASH_MISO    // SPI flash IO pins
  );

  wire clkout;
  wire resetn;

  wire [31:0] mem_addr;
  wire [31:0] mem_rdata;
  wire        mem_rbusy;
  wire mem_rstrb;
  wire [31:0] mem_wdata;
  wire [3:0]  mem_wmask;

  Processor CPU(
    .clk(clkout),
    .resetn(resetn),   
    .mem_addr(mem_addr),
    .mem_rdata(mem_rdata),
    .mem_rstrb(mem_rstrb),
    .mem_rbusy(mem_rbusy),
    .mem_wdata(mem_wdata),
    .mem_wmask(mem_wmask)
  );

  wire [31:0] ram_rdata;
  wire [29:0] mem_wordaddr = mem_addr[31:2];
  wire isSPIFlash  = mem_addr[25];
  wire is_io = mem_addr[25:24] == 2'b01;
  wire is_ram = !(mem_addr[25] | mem_addr[24]);
  wire mem_wstrb = |mem_wmask;   //bitwise or entire bus

  Memory RAM(
    .clk(clkout),
    .mem_addr(mem_addr),
    .mem_rdata(ram_rdata),
    .mem_rstrb(is_ram & mem_rstrb),
    .mem_wdata(mem_wdata),
    .mem_wmask({4{is_ram}} & mem_wmask)
  );

  wire [31:0] SPIFlash_rdata;
  wire SPIFlash_rbusy;
  MappedSPIFlash SPIFlash(
    .clk(clk),
    .word_address(mem_wordaddr[21:0]),
    .rdata(SPIFlash_rdata),
    .rstrb(isSPIFlash & mem_rstrb),
    .rbusy(SPIFlash_rbusy),
    .CLK(SPIFLASH_CLK),
    .CS_N(SPIFLASH_CS_N),
    .MOSI(SPIFLASH_MOSI),
    .MISO(SPIFLASH_MISO)			   
  );
  // Memory-mapped IO in IO page, 1-hot addressing in word address.
  localparam  IO_LEDS_bit   = 0;  // write led bits
  localparam  IO_UART_DAT_bit = 1;  // write data to send 8 bits
  localparam  IO_UART_CNTL_bit = 2;  // Read Status

  always @ (posedge clkout) begin
    if(is_io & mem_wstrb & mem_wordaddr[IO_LEDS_bit]) begin
      LEDS <= mem_wdata[3:0];
    end
  end

  wire uart_valid = is_io & mem_wstrb & mem_wordaddr[IO_UART_DAT_bit];
  wire uart_ready;

  corescore_emitter_uart #(
    .clk_freq_hz(100*1000000),
    .baud_rate(1000000)
  ) UART(
    .i_clk(clkout),
    .i_rst(resetn),
    .i_data(mem_wdata[7:0]),
    .i_valid(uart_valid),
    .o_ready(uart_ready),
    .o_uart_tx(TXD)
  );

  wire [31:0] io_rdata =
        mem_wordaddr[IO_UART_CNTL_bit] ? {22'b0 , !uart_ready , 9'b0}
                                   : 32'b0
  ;

  assign mem_rdata = is_ram     ? ram_rdata : 
                     isSPIFlash ? SPIFlash_rdata :
                                  io_rdata
  ;

  assign mem_rbusy = SPIFlash_rbusy;
   
  `ifdef BENCH
    always @ (posedge clkout) begin
      if(uart_valid)begin
        $write("%c" , mem_wdata[7:0]);
        $fflush(32'h8000_0001);
      end
    end
  `endif
    Clockworks CW(
      .CLK(CLK),
      .RESET(RESET),
      .clk(clkout),
      .resetn(resetn)
  );
endmodule
