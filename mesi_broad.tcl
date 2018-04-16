#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script

#   mesi_isc/src/rtl/mesi_isc_breq_fifos_cntl.v \
#   mesi_isc/src/rtl/mesi_isc_breq_fifos.v \
#   mesi_isc/src/rtl/mesi_isc_broad_cntl.v \
#   mesi_isc/src/rtl/mesi_isc_broad.v \
#   mesi_isc/src/rtl/mesi_isc.v \
#   mesi_isc/src/rtl/mesi_isc_define.v \

#Reading the files 
analyze -v2k {
   mesi_isc/src/rtl/mesi_isc_define.v \
   mesi_isc/src/rtl/mesi_isc_basic_fifo.v \
   mesi_isc/src/rtl/mesi_isc_broad_cntl.v \
   mesi_isc/src/rtl/mesi_isc_broad.v \
};

analyze -sv {mesi_broad_test.sv};

#Elaborating the design
elaborate -top {mesi_isc_broad};

#You will need to add commands below

#Set the clock
clock clk;

#Set Reset
reset -expression {rst};

#Prove all
prove -bg -all

