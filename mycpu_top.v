module mycpu_top(
    input  wire        clk,
    input  wire        resetn,
    // inst sram interface
    output wire        inst_sram_en,
    output wire [3:0]  inst_sram_we,
    output wire [31:0] inst_sram_addr,
    output wire [31:0] inst_sram_wdata,
    input  wire [31:0] inst_sram_rdata,
    // data sram interface
    output wire        data_sram_en,
    output wire [3:0]  data_sram_we,
    output wire [31:0] data_sram_addr,
    output wire [31:0] data_sram_wdata,
    input  wire [31:0] data_sram_rdata,
    // trace debug interface
    output wire [31:0] debug_wb_pc,
    output wire [ 3:0] debug_wb_rf_we,
    output wire [ 4:0] debug_wb_rf_wnum,
    output wire [31:0] debug_wb_rf_wdata
);
reg         reset;
always @(posedge clk) reset <= ~resetn;

wire [31:0] seq_pc;
wire [31:0] nextpc;
wire        br_taken;
wire [31:0] br_target;

wire [31:0] f_inst;
reg [31:0] D_inst;

wire pre_f_alllowin;
wire f_allowin;
wire F_readygo;
wire F2D_valid;
reg F_valid;

wire d_allowin;
wire D_readygo;
wire D2E_valid;
reg D_valid;

wire e_allowin;
wire E_readygo;
wire E2M_valid;
reg E_valid;

wire m_allowin;
wire M_readygo;
wire M2W_valid;
reg M_valid;

wire w_allowin;
wire W_readygo;
reg W_valid;



reg  [31:0] F_PC;
reg  [31:0] D_PC;
reg  [31:0] E_PC;
reg  [31:0] M_PC;
reg  [31:0] W_PC;

wire [11:0] d_alu_op;
reg  [11:0] E_alu_op;

wire        load_op;

wire        d_src1_is_pc;
wire        d_src2_is_imm;
reg         E_src1_is_pc;
reg         E_src2_is_imm;

wire        d_res_from_mem;
reg         E_res_from_mem;
reg         M_res_from_mem;

wire        d_dst_is_r1;

wire        d_gr_we;
reg         E_gr_we;
reg         M_gr_we;
reg         W_gr_we;

wire [3:0]  d_mem_we;
reg  [3:0]  E_mem_we;

wire        d_mem_en;
reg         E_mem_en;

wire        d_src_reg_is_rd;

wire [4: 0] d_dest;
reg  [4: 0] E_dest;
reg  [4: 0] M_dest;
reg  [4: 0] W_dest;

wire [31:0] d_rj_value;
reg  [31:0] E_rj_value;

wire [31:0] d_rkd_value;
reg  [31:0] E_rkd_value;

wire        rj_eq_rd;

wire [31:0] d_imm;
reg  [31:0] E_imm;

wire [31:0] d_br_offs;

wire [31:0] d_jirl_offs;



wire [ 5:0] op_31_26;
wire [ 3:0] op_25_22;
wire [ 1:0] op_21_20;
wire [ 4:0] op_19_15;
wire [ 4:0] rd;
wire [ 4:0] rj;
wire [ 4:0] rk;
wire [11:0] i12;
wire [19:0] i20;
wire [15:0] i16;
wire [25:0] i26;

wire [63:0] op_31_26_d;
wire [15:0] op_25_22_d;
wire [ 3:0] op_21_20_d;
wire [31:0] op_19_15_d;

wire        inst_add_w;
wire        inst_sub_w;
wire        inst_slt;
wire        inst_sltu;
wire        inst_nor;
wire        inst_and;
wire        inst_or;
wire        inst_xor;
wire        inst_slli_w;
wire        inst_srli_w;
wire        inst_srai_w;
wire        inst_addi_w;
wire        inst_ld_w;
wire        inst_st_w;
wire        inst_jirl;
wire        inst_b;
wire        inst_bl;
wire        inst_beq;
wire        inst_bne;
wire        inst_lu12i_w;

wire        need_ui5;
wire        need_si12;
wire        need_si16;
wire        need_si20;
wire        need_si26;
wire        src2_is_4;

wire [ 4:0] rf_raddr1;
wire [31:0] rf_rdata1;
wire [ 4:0] rf_raddr2;
wire [31:0] rf_rdata2;



wire        rf_we   ;
wire [ 4:0] rf_waddr;
wire [31:0] rf_wdata;




wire [31:0] alu_src1   ;
wire [31:0] alu_src2   ;
wire [31:0] e_alu_result ;
reg  [31:0] M_alu_result ;




wire [31:0] mem_result;
wire [31:0] m_final_result;       //error2: declare final_result
reg  [31:0] W_final_result;

assign seq_pc       = F_PC + 32'h4;
assign nextpc       = br_taken ? br_target : seq_pc;


////////////////////////////////////////////////////////////////
///////////////////////////////////////////
//IF流水级
assign F_readygo = 1'b1;
assign pre_f_allowin = !F_valid | F_readygo & f_allowin;
assign F2D_valid = F_valid & F_readygo;
always @(posedge clk) begin
	//trick: to make nextpc be 0x1c000000 during reset 
	if(reset)
	begin
		F_valid <= 1'b0;
		F_PC <= 32'h1bfffffc;
	end
	else if(pre_f_allowin)
	begin
		F_valid <= 1'b1;
		F_PC <= nextpc;
	end

end
////////////////////////////////////////////////////////////////


assign inst_sram_en = 1'b1;
assign inst_sram_we = 4'b0000; 
assign inst_sram_addr  = nextpc;
assign inst_sram_wdata = 32'b0;
assign f_inst            = inst_sram_rdata;



////////////////////////////////////////////////////////////////
///////////////////////////////////////////
//ID流水级
assign D_readygo = 1'b1;
assign f_allowin = !D_valid | D_readygo & d_allowin;
assign D2E_valid = D_valid & D_readygo;
always @(posedge clk)
begin
	if(reset)
		D_valid <= 1'b0;
	else if(f_allowin)
		D_valid <= F2D_valid;
	if(F2D_valid & f_allowin)
	begin
		D_PC <= F_PC;
		D_inst <= f_inst;
	end
end
////////////////////////////////////////////////////////////////



assign op_31_26  = D_inst[31:26];
assign op_25_22  = D_inst[25:22];
assign op_21_20  = D_inst[21:20];
assign op_19_15  = D_inst[19:15];

assign rd   = D_inst[ 4: 0];
assign rj   = D_inst[ 9: 5];
assign rk   = D_inst[14:10];

assign i12  = D_inst[21:10];
assign i20  = D_inst[24: 5];
assign i16  = D_inst[25:10];
assign i26  = {D_inst[ 9: 0], D_inst[25:10]};

decoder_6_64 u_dec0(.in(op_31_26 ), .out(op_31_26_d ));
decoder_4_16 u_dec1(.in(op_25_22 ), .out(op_25_22_d ));
decoder_2_4  u_dec2(.in(op_21_20 ), .out(op_21_20_d ));
decoder_5_32 u_dec3(.in(op_19_15 ), .out(op_19_15_d ));

assign inst_add_w  = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h00];
assign inst_sub_w  = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h02];
assign inst_slt    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h04];
assign inst_sltu   = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h05];
assign inst_nor    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h08];
assign inst_and    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h09];
assign inst_or     = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h0a];
assign inst_xor    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h0b];
assign inst_slli_w = op_31_26_d[6'h00] & op_25_22_d[4'h1] & op_21_20_d[2'h0] & op_19_15_d[5'h01];
assign inst_srli_w = op_31_26_d[6'h00] & op_25_22_d[4'h1] & op_21_20_d[2'h0] & op_19_15_d[5'h09];
assign inst_srai_w = op_31_26_d[6'h00] & op_25_22_d[4'h1] & op_21_20_d[2'h0] & op_19_15_d[5'h11];
assign inst_addi_w = op_31_26_d[6'h00] & op_25_22_d[4'ha];
assign inst_ld_w   = op_31_26_d[6'h0a] & op_25_22_d[4'h2];
assign inst_st_w   = op_31_26_d[6'h0a] & op_25_22_d[4'h6];
assign inst_jirl   = op_31_26_d[6'h13];
assign inst_b      = op_31_26_d[6'h14];
assign inst_bl     = op_31_26_d[6'h15];
assign inst_beq    = op_31_26_d[6'h16];
assign inst_bne    = op_31_26_d[6'h17];
assign inst_lu12i_w= op_31_26_d[6'h05] & ~D_inst[25];

assign d_alu_op[ 0] = inst_add_w | inst_addi_w | inst_ld_w | inst_st_w
                    | inst_jirl | inst_bl;
assign d_alu_op[ 1] = inst_sub_w;
assign d_alu_op[ 2] = inst_slt;
assign d_alu_op[ 3] = inst_sltu;
assign d_alu_op[ 4] = inst_and;
assign d_alu_op[ 5] = inst_nor;
assign d_alu_op[ 6] = inst_or;
assign d_alu_op[ 7] = inst_xor;
assign d_alu_op[ 8] = inst_slli_w;
assign d_alu_op[ 9] = inst_srli_w;
assign d_alu_op[10] = inst_srai_w;
assign d_alu_op[11] = inst_lu12i_w;

assign need_ui5   =  inst_slli_w | inst_srli_w | inst_srai_w;
assign need_si12  =  inst_addi_w | inst_ld_w | inst_st_w;
assign need_si16  =  inst_jirl | inst_beq | inst_bne;
assign need_si20  =  inst_lu12i_w;
assign need_si26  =  inst_b | inst_bl;
assign src2_is_4  =  inst_jirl | inst_bl;

assign d_imm = src2_is_4 ? 32'h4                      :
             need_si20 ? {i20[19:0], 12'b0}         :
/*need_ui5 || need_si12*/{{20{i12[11]}}, i12[11:0]} ;

assign d_br_offs = need_si26 ? {{ 4{i26[25]}}, i26[25:0], 2'b0} :
                             {{14{i16[15]}}, i16[15:0], 2'b0} ;

assign d_jirl_offs = {{14{i16[15]}}, i16[15:0], 2'b0};

assign d_src_reg_is_rd = inst_beq | inst_bne | inst_st_w;

assign d_src1_is_pc    = inst_jirl | inst_bl;

assign d_src2_is_imm   = inst_slli_w |
                       inst_srli_w |
                       inst_srai_w |
                       inst_addi_w |
                       inst_ld_w   |
                       inst_st_w   |
                       inst_lu12i_w|
                       inst_jirl   |
                       inst_bl     ;

assign d_res_from_mem  = inst_ld_w;
assign d_dst_is_r1     = inst_bl;
assign d_gr_we         = ~inst_st_w & ~inst_beq & ~inst_bne & ~inst_b;        //error4: delete ~inst_bl
assign d_mem_we        = {4{inst_st_w}};
assign d_mem_en        = inst_ld_w | inst_st_w;
assign d_dest          = d_dst_is_r1 ? 5'd1 : rd;

assign rf_raddr1 = rj;
assign rf_raddr2 = d_src_reg_is_rd ? rd :rk;
regfile u_regfile(
    .clk    (clk      ),
    .raddr1 (rf_raddr1),
    .rdata1 (rf_rdata1),
    .raddr2 (rf_raddr2),
    .rdata2 (rf_rdata2),
    .we     (rf_we    ),
    .waddr  (rf_waddr ),
    .wdata  (rf_wdata )
    );

assign d_rj_value  = rf_rdata1;
assign d_rkd_value = rf_rdata2;

assign rj_eq_rd = (d_rj_value == d_rkd_value);
assign br_taken = (   inst_beq  &  rj_eq_rd
                   || inst_bne  & !rj_eq_rd
                   || inst_jirl
                   || inst_bl
                   || inst_b
                  ) & D_valid;
assign br_target = (inst_beq || inst_bne || inst_bl || inst_b) ? (D_PC + d_br_offs) :
                                                   /*inst_jirl*/ (d_rj_value + d_jirl_offs);




////////////////////////////////////////////////////////////////
///////////////////////////////////////////
//EX流水级
assign E_readygo = 1'b1;
assign d_allowin = !E_valid | E_readygo & e_allowin;
assign E2M_valid = E_valid & E_readygo;

always @(posedge clk)
begin
	if(reset)
		E_valid <= 1'b0;
	else if(d_allowin)
		E_valid <= D2E_valid;


	if(D2E_valid & d_allowin)
	begin
		E_PC <= D_PC;
		E_alu_op <= d_alu_op;
		E_src1_is_pc <= d_src1_is_pc;
		E_src2_is_imm <= d_src2_is_imm;
		E_res_from_mem <= d_res_from_mem;
		E_gr_we <= d_gr_we;
		E_mem_we <= d_mem_we;
		E_mem_en <= d_mem_en;
		E_dest <= d_dest;
		E_rj_value <= d_rj_value;
		E_rkd_value <= d_rkd_value;
		E_imm <= d_imm;
	end

end
////////////////////////////////////////////////////////////////




assign alu_src1 = E_src1_is_pc  ? E_PC[31:0] : E_rj_value;
assign alu_src2 = E_src2_is_imm ? E_imm : E_rkd_value;

alu u_alu(
    .alu_op     (E_alu_op    ),
    .alu_src1   (alu_src1  ),           //error3: src2->src1
    .alu_src2   (alu_src2  ),
    .alu_result (e_alu_result)
    );


assign data_sram_we    = {4{E_valid}} & E_mem_we;
assign data_sram_en    = E_mem_en;
assign data_sram_addr  = e_alu_result;
assign data_sram_wdata = E_rkd_value;


////////////////////////////////////////////////////////////////
///////////////////////////////////////////
//MEM流水级
assign M_readygo = 1'b1;
assign e_allowin = !M_valid | M_readygo & m_allowin;
assign M2W_valid = M_valid & M_readygo;
always @(posedge clk)
begin
	if(reset)
		M_valid <= 1'b0;
	else if(e_allowin)
		M_valid <= E2M_valid;

	if(E2M_valid & e_allowin)
	begin
		M_PC <= E_PC;
		M_alu_result <= e_alu_result;
		M_dest <= E_dest;
		M_gr_we <= E_gr_we;
		M_res_from_mem <= E_res_from_mem;
	end
end
////////////////////////////////////////////////////////////////


assign mem_result   = data_sram_rdata;
assign m_final_result = M_res_from_mem ? mem_result : M_alu_result;


////////////////////////////////////////////////////////////////
///////////////////////////////////////////
//WB流水级
assign W_readygo = 1'b1;
assign m_allowin = !W_valid | W_readygo & w_allowin;
always @(posedge clk)
begin
	if(reset)
		W_valid <= 1'b0;
	else if(m_allowin)
		W_valid <= M2W_valid;
	if(M2W_valid & m_allowin)
	begin
		W_PC <= M_PC;
		W_dest <= M_dest;
		W_gr_we <= M_gr_we;
		W_final_result <= m_final_result;
	end
end
////////////////////////////////////////////////////////////////


assign w_allowin = 1'b1;

assign rf_we    = W_gr_we & W_valid;
assign rf_waddr = W_dest;
assign rf_wdata = W_final_result;

// debug info generate
assign debug_wb_pc       = W_PC;
assign debug_wb_rf_we   = {4{rf_we}};       //error1: wen->we
assign debug_wb_rf_wnum  = W_dest;
assign debug_wb_rf_wdata = W_final_result;

endmodule
