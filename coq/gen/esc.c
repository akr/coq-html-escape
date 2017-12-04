buffer
n3_trec_html_escape(buffer v2_buf, byteptr v1_ptr, nat v0_n)
{
  n3_trec_html_escape:;
  switch (sw_nat(v0_n))
  {
    case_O_nat: { return v2_buf; }
    case_S_nat: {
      nat v4_n_ = field0_S_nat(v0_n);
      ascii v5_a = n1_bptrget(v1_ptr);
      prod_byteptr_nat v6_p = n1_html_escape_byte_table(v5_a);
      byteptr v7_escptr = field0_pair_prod_byteptr_nat(v6_p);
      nat v8_escn = field1_pair_prod_byteptr_nat(v6_p);
      buffer v9_b = n3_bufaddmem(v2_buf, v7_escptr, v8_escn);
      nat v10_n = n0_O();
      nat v11_n = n1_S(v10_n);
      byteptr v12_b = n2_bptradd(v1_ptr, v11_n);
      v2_buf = v9_b;
      v1_ptr = v12_b;
      v0_n = v4_n_;
      goto n3_trec_html_escape;
    }
  }
}
buffer
n4_sse_html_escape(buffer v16_buf, byteptr v15_ptr, nat v14_m, nat v13_n)
{
  n4_sse_html_escape:;
  switch (sw_nat(v13_n))
  {
    case_O_nat: { return n3_bufaddmem(v16_buf, v15_ptr, v14_m); }
    case_S_nat: {
      nat v18_n_ = field0_S_nat(v13_n);
      byteptr v19_p1 = n2_bptradd(v15_ptr, v14_m);
      nat v20_n = n0_O();
      nat v21_n = n1_S(v20_n);
      nat v22_n = n1_S(v21_n);
      nat v23_n = n1_S(v22_n);
      nat v24_n = n1_S(v23_n);
      nat v25_n = n1_S(v24_n);
      nat v26_n = n1_S(v25_n);
      nat v27_n = n1_S(v26_n);
      nat v28_n = n1_S(v27_n);
      nat v29_n = n1_S(v28_n);
      nat v30_n = n1_S(v29_n);
      nat v31_n = n1_S(v30_n);
      nat v32_n = n1_S(v31_n);
      nat v33_n = n1_S(v32_n);
      nat v34_n = n1_S(v33_n);
      nat v35_n = n1_S(v34_n);
      bool v36_b = n2_leq(v13_n, v35_n);
      switch (sw_bool(v36_b))
      {
        case_true_bool: {
          buffer v37_b = n3_bufaddmem(v16_buf, v15_ptr, v14_m);
          return n3_trec_html_escape(v37_b, v19_p1, v13_n);
        }
        case_false_bool: {
          m128 v38_m = n0_chars_to_escape();
          nat v39_n = n0_num_chars_to_escape();
          m128 v40_m = n1_m128_of_bptr(v19_p1);
          nat v41_n = n0_O();
          nat v42_n = n1_S(v41_n);
          nat v43_n = n1_S(v42_n);
          nat v44_n = n1_S(v43_n);
          nat v45_n = n1_S(v44_n);
          nat v46_n = n1_S(v45_n);
          nat v47_n = n1_S(v46_n);
          nat v48_n = n1_S(v47_n);
          nat v49_n = n1_S(v48_n);
          nat v50_n = n1_S(v49_n);
          nat v51_n = n1_S(v50_n);
          nat v52_n = n1_S(v51_n);
          nat v53_n = n1_S(v52_n);
          nat v54_n = n1_S(v53_n);
          nat v55_n = n1_S(v54_n);
          nat v56_n = n1_S(v55_n);
          nat v57_n = n1_S(v56_n);
          nat
          v58_i
          =
          n4_cmpestri_ubyte_eqany_ppol_lsig(v38_m,
          v39_n,
          v40_m,
          v57_n);
          nat v59_n = n0_O();
          nat v60_n = n1_S(v59_n);
          nat v61_n = n1_S(v60_n);
          nat v62_n = n1_S(v61_n);
          nat v63_n = n1_S(v62_n);
          nat v64_n = n1_S(v63_n);
          nat v65_n = n1_S(v64_n);
          nat v66_n = n1_S(v65_n);
          nat v67_n = n1_S(v66_n);
          nat v68_n = n1_S(v67_n);
          nat v69_n = n1_S(v68_n);
          nat v70_n = n1_S(v69_n);
          nat v71_n = n1_S(v70_n);
          nat v72_n = n1_S(v71_n);
          nat v73_n = n1_S(v72_n);
          nat v74_n = n1_S(v73_n);
          nat v75_n = n1_S(v74_n);
          bool v76_b = n2_leq(v75_n, v58_i);
          switch (sw_bool(v76_b))
          {
            case_true_bool: {
              nat v77_n = n0_O();
              nat v78_n = n1_S(v77_n);
              nat v79_n = n1_S(v78_n);
              nat v80_n = n1_S(v79_n);
              nat v81_n = n1_S(v80_n);
              nat v82_n = n1_S(v81_n);
              nat v83_n = n1_S(v82_n);
              nat v84_n = n1_S(v83_n);
              nat v85_n = n1_S(v84_n);
              nat v86_n = n1_S(v85_n);
              nat v87_n = n1_S(v86_n);
              nat v88_n = n1_S(v87_n);
              nat v89_n = n1_S(v88_n);
              nat v90_n = n1_S(v89_n);
              nat v91_n = n1_S(v90_n);
              nat v92_n = n1_S(v91_n);
              nat v93_n = n1_S(v92_n);
              nat v94_n = n2_addn(v14_m, v93_n);
              nat v95_n = n0_O();
              nat v96_n = n1_S(v95_n);
              nat v97_n = n1_S(v96_n);
              nat v98_n = n1_S(v97_n);
              nat v99_n = n1_S(v98_n);
              nat v100_n = n1_S(v99_n);
              nat v101_n = n1_S(v100_n);
              nat v102_n = n1_S(v101_n);
              nat v103_n = n1_S(v102_n);
              nat v104_n = n1_S(v103_n);
              nat v105_n = n1_S(v104_n);
              nat v106_n = n1_S(v105_n);
              nat v107_n = n1_S(v106_n);
              nat v108_n = n1_S(v107_n);
              nat v109_n = n1_S(v108_n);
              nat v110_n = n1_S(v109_n);
              nat v111_n = n2_subn(v18_n_, v110_n);
              v14_m = v94_n;
              v13_n = v111_n;
              goto n4_sse_html_escape;
            }
            case_false_bool: {
              nat v112_n = n2_addn(v14_m, v58_i);
              buffer v113_buf2 = n3_bufaddmem(v16_buf, v15_ptr, v112_n);
              nat v114_n = n2_addn(v14_m, v58_i);
              byteptr v115_p2 = n2_bptradd(v15_ptr, v114_n);
              ascii v116_c = n1_bptrget(v115_p2);
              nat v117_n = n0_O();
              nat v118_n = n1_S(v117_n);
              byteptr v119_p3 = n2_bptradd(v115_p2, v118_n);
              prod_byteptr_nat v120_p = n1_html_escape_byte_table(v116_c);
              byteptr v121_escptr = field0_pair_prod_byteptr_nat(v120_p);
              nat v122_escn = field1_pair_prod_byteptr_nat(v120_p);
              buffer
              v123_buf3
              =
              n3_bufaddmem(v113_buf2,
              v121_escptr,
              v122_escn);
              nat v124_n = n0_O();
              nat v125_n = n2_subn(v18_n_, v58_i);
              v16_buf = v123_buf3;
              v15_ptr = v119_p3;
              v14_m = v124_n;
              v13_n = v125_n;
              goto n4_sse_html_escape;
            }
          }
        }
      }
    }
  }
}
prod_prod_buffer_byteptr_nat
n6_sse_html_escape2_dense(buffer v131_buf,
                          byteptr v130_ptr,
                          nat v129_m,
                          nat v128_i,
                          nat v127_mask,
                          m128 v126_bytes)
{
  n6_sse_html_escape2_dense:;
  switch (sw_nat(v128_i))
  {
    case_O_nat: {
      prod_buffer_byteptr
      v133_p
      =
      n2_pair_buffer_byteptr(v131_buf,
      v130_ptr);
      return n2_pair_prod_buffer_byteptr_nat(v133_p, v129_m);
    }
    case_S_nat: {
      nat v134_i_ = field0_S_nat(v128_i);
      bool v135_b = n1_odd(v127_mask);
      switch (sw_bool(v135_b))
      {
        case_true_bool: {
          buffer v136_buf1;
          switch (sw_nat(v129_m))
          {
            case_O_nat: { v136_buf1 = v131_buf; break; }
            case_S_nat: {
              nat v137_n = field0_S_nat(v129_m);
              v136_buf1 = n3_bufaddmem(v131_buf, v130_ptr, v129_m);
              break;
            }
          }
          ascii v138_c = n1_m128_firstbyte(v126_bytes);
          m128 v139_rest = n1_m128_restbytes(v126_bytes);
          prod_byteptr_nat v140_p = n1_html_escape_byte_table(v138_c);
          byteptr v141_escptr = field0_pair_prod_byteptr_nat(v140_p);
          nat v142_escn = field1_pair_prod_byteptr_nat(v140_p);
          buffer v143_buf2 = n3_bufaddmem(v136_buf1, v141_escptr, v142_escn);
          nat v144_n = n1_S(v129_m);
          byteptr v145_ptr2 = n2_bptradd(v130_ptr, v144_n);
          nat v146_n = n0_O();
          nat v147_n = n1_half(v127_mask);
          v131_buf = v143_buf2;
          v130_ptr = v145_ptr2;
          v129_m = v146_n;
          v128_i = v134_i_;
          v127_mask = v147_n;
          v126_bytes = v139_rest;
          goto n6_sse_html_escape2_dense;
        }
        case_false_bool: {
          m128 v148_rest = n1_m128_restbytes(v126_bytes);
          nat v149_n = n1_S(v129_m);
          nat v150_n = n1_half(v127_mask);
          v129_m = v149_n;
          v128_i = v134_i_;
          v127_mask = v150_n;
          v126_bytes = v148_rest;
          goto n6_sse_html_escape2_dense;
        }
      }
    }
  }
}
prod_prod_buffer_byteptr_nat
n4_sse_html_escape2_aligned(buffer v154_buf,
                            byteptr v153_ptr,
                            nat v152_m,
                            nat v151_nn)
{
  n4_sse_html_escape2_aligned:;
  switch (sw_nat(v151_nn))
  {
    case_O_nat: {
      prod_buffer_byteptr
      v156_p
      =
      n2_pair_buffer_byteptr(v154_buf,
      v153_ptr);
      return n2_pair_prod_buffer_byteptr_nat(v156_p, v152_m);
    }
    case_S_nat: {
      nat v157_nn_ = field0_S_nat(v151_nn);
      byteptr v158_p1 = n2_bptradd(v153_ptr, v152_m);
      m128 v159_bytes16 = n1_m128_of_bptr(v158_p1);
      m128 v160_m = n0_chars_to_escape();
      nat v161_n = n0_num_chars_to_escape();
      nat v162_n = n0_O();
      nat v163_n = n1_S(v162_n);
      nat v164_n = n1_S(v163_n);
      nat v165_n = n1_S(v164_n);
      nat v166_n = n1_S(v165_n);
      nat v167_n = n1_S(v166_n);
      nat v168_n = n1_S(v167_n);
      nat v169_n = n1_S(v168_n);
      nat v170_n = n1_S(v169_n);
      nat v171_n = n1_S(v170_n);
      nat v172_n = n1_S(v171_n);
      nat v173_n = n1_S(v172_n);
      nat v174_n = n1_S(v173_n);
      nat v175_n = n1_S(v174_n);
      nat v176_n = n1_S(v175_n);
      nat v177_n = n1_S(v176_n);
      nat v178_n = n1_S(v177_n);
      bool
      v179_c
      =
      n4_cmpestrc_ubyte_eqany_ppol_lsig_bitmask(v160_m,
      v161_n,
      v159_bytes16,
      v178_n);
      m128 v180_m = n0_chars_to_escape();
      nat v181_n = n0_num_chars_to_escape();
      nat v182_n = n0_O();
      nat v183_n = n1_S(v182_n);
      nat v184_n = n1_S(v183_n);
      nat v185_n = n1_S(v184_n);
      nat v186_n = n1_S(v185_n);
      nat v187_n = n1_S(v186_n);
      nat v188_n = n1_S(v187_n);
      nat v189_n = n1_S(v188_n);
      nat v190_n = n1_S(v189_n);
      nat v191_n = n1_S(v190_n);
      nat v192_n = n1_S(v191_n);
      nat v193_n = n1_S(v192_n);
      nat v194_n = n1_S(v193_n);
      nat v195_n = n1_S(v194_n);
      nat v196_n = n1_S(v195_n);
      nat v197_n = n1_S(v196_n);
      nat v198_n = n1_S(v197_n);
      m128
      v199_mask_
      =
      n4_cmpestrm_ubyte_eqany_ppol_lsig_bitmask(v180_m,
      v181_n,
      v159_bytes16,
      v198_n);
      switch (sw_bool(v179_c))
      {
        case_true_bool: {
          nat v200_mask = n1_lo64_of_m128(v199_mask_);
          nat v201_n = n0_O();
          nat v202_n = n1_S(v201_n);
          nat v203_n = n1_S(v202_n);
          nat v204_n = n1_S(v203_n);
          nat v205_n = n1_S(v204_n);
          nat v206_n = n1_S(v205_n);
          nat v207_n = n1_S(v206_n);
          nat v208_n = n1_S(v207_n);
          nat v209_n = n1_S(v208_n);
          nat v210_n = n1_S(v209_n);
          nat v211_n = n1_S(v210_n);
          nat v212_n = n1_S(v211_n);
          nat v213_n = n1_S(v212_n);
          nat v214_n = n1_S(v213_n);
          nat v215_n = n1_S(v214_n);
          nat v216_n = n1_S(v215_n);
          nat v217_n = n1_S(v216_n);
          prod_prod_buffer_byteptr_nat
          v218_p
          =
          n6_sse_html_escape2_dense(v154_buf,
          v153_ptr,
          v152_m,
          v217_n,
          v200_mask,
          v159_bytes16);
          prod_buffer_byteptr
          v219_p
          =
          field0_pair_prod_prod_buffer_byteptr_nat(v218_p);
          nat v220_m2 = field1_pair_prod_prod_buffer_byteptr_nat(v218_p);
          buffer v221_buf2 = field0_pair_prod_buffer_byteptr(v219_p);
          byteptr v222_ptr2 = field1_pair_prod_buffer_byteptr(v219_p);
          v154_buf = v221_buf2;
          v153_ptr = v222_ptr2;
          v152_m = v220_m2;
          v151_nn = v157_nn_;
          goto n4_sse_html_escape2_aligned;
        }
        case_false_bool: {
          nat v223_n = n0_O();
          nat v224_n = n1_S(v223_n);
          nat v225_n = n1_S(v224_n);
          nat v226_n = n1_S(v225_n);
          nat v227_n = n1_S(v226_n);
          nat v228_n = n1_S(v227_n);
          nat v229_n = n1_S(v228_n);
          nat v230_n = n1_S(v229_n);
          nat v231_n = n1_S(v230_n);
          nat v232_n = n1_S(v231_n);
          nat v233_n = n1_S(v232_n);
          nat v234_n = n1_S(v233_n);
          nat v235_n = n1_S(v234_n);
          nat v236_n = n1_S(v235_n);
          nat v237_n = n1_S(v236_n);
          nat v238_n = n1_S(v237_n);
          nat v239_n = n1_S(v238_n);
          nat v240_n = n2_addn(v152_m, v239_n);
          v152_m = v240_n;
          v151_nn = v157_nn_;
          goto n4_sse_html_escape2_aligned;
        }
      }
    }
  }
}
buffer
n3_sse_html_escape2(buffer v243_buf, byteptr v242_ptr, nat v241_n)
{
  nat v244_n = n0_O();
  nat v245_n = n1_S(v244_n);
  nat v246_n = n1_S(v245_n);
  nat v247_n = n1_S(v246_n);
  nat v248_n = n1_S(v247_n);
  nat v249_n = n1_S(v248_n);
  nat v250_n = n1_S(v249_n);
  nat v251_n = n1_S(v250_n);
  nat v252_n = n1_S(v251_n);
  nat v253_n = n1_S(v252_n);
  nat v254_n = n1_S(v253_n);
  nat v255_n = n1_S(v254_n);
  nat v256_n = n1_S(v255_n);
  nat v257_n = n1_S(v256_n);
  nat v258_n = n1_S(v257_n);
  nat v259_n = n1_S(v258_n);
  bool v260_b = n2_leq(v241_n, v259_n);
  switch (sw_bool(v260_b))
  {
    case_true_bool: {
      return n3_trec_html_escape(v243_buf, v242_ptr, v241_n);
    }
    case_false_bool: {
      nat v261_n = n0_O();
      nat v262_n = n1_S(v261_n);
      nat v263_n = n1_S(v262_n);
      nat v264_n = n1_S(v263_n);
      nat v265_n = n1_S(v264_n);
      nat v266_n = n1_S(v265_n);
      nat v267_n = n1_S(v266_n);
      nat v268_n = n1_S(v267_n);
      nat v269_n = n1_S(v268_n);
      nat v270_n = n1_S(v269_n);
      nat v271_n = n1_S(v270_n);
      nat v272_n = n1_S(v271_n);
      nat v273_n = n1_S(v272_n);
      nat v274_n = n1_S(v273_n);
      nat v275_n = n1_S(v274_n);
      nat v276_n = n1_S(v275_n);
      nat v277_n = n1_S(v276_n);
      nat v278_left_align = n2_align_of_bptr(v277_n, v242_ptr);
      nat v279_left_len;
      switch (sw_nat(v278_left_align))
      {
        case_O_nat: { v279_left_len = n0_O(); break; }
        case_S_nat: {
          nat v280_n = field0_S_nat(v278_left_align);
          nat v281_n = n0_O();
          nat v282_n = n1_S(v281_n);
          nat v283_n = n1_S(v282_n);
          nat v284_n = n1_S(v283_n);
          nat v285_n = n1_S(v284_n);
          nat v286_n = n1_S(v285_n);
          nat v287_n = n1_S(v286_n);
          nat v288_n = n1_S(v287_n);
          nat v289_n = n1_S(v288_n);
          nat v290_n = n1_S(v289_n);
          nat v291_n = n1_S(v290_n);
          nat v292_n = n1_S(v291_n);
          nat v293_n = n1_S(v292_n);
          nat v294_n = n1_S(v293_n);
          nat v295_n = n1_S(v294_n);
          nat v296_n = n1_S(v295_n);
          nat v297_n = n1_S(v296_n);
          v279_left_len = n2_subn(v297_n, v278_left_align);
          break;
        }
      }
      buffer
      v298_buf2
      =
      n3_trec_html_escape(v243_buf,
      v242_ptr,
      v279_left_len);
      byteptr v299_ptr2 = n2_bptradd(v242_ptr, v279_left_len);
      nat v300_n2 = n2_subn(v241_n, v279_left_len);
      nat v301_n = n0_O();
      nat v302_n = n1_S(v301_n);
      nat v303_n = n1_S(v302_n);
      nat v304_n = n1_S(v303_n);
      nat v305_n = n1_S(v304_n);
      nat v306_n = n1_S(v305_n);
      nat v307_n = n1_S(v306_n);
      nat v308_n = n1_S(v307_n);
      nat v309_n = n1_S(v308_n);
      nat v310_n = n1_S(v309_n);
      nat v311_n = n1_S(v310_n);
      nat v312_n = n1_S(v311_n);
      nat v313_n = n1_S(v312_n);
      nat v314_n = n1_S(v313_n);
      nat v315_n = n1_S(v314_n);
      nat v316_n = n1_S(v315_n);
      nat v317_n = n1_S(v316_n);
      nat v318_mid_count = n2_divn(v300_n2, v317_n);
      nat v319_n = n0_O();
      nat v320_n = n1_S(v319_n);
      nat v321_n = n1_S(v320_n);
      nat v322_n = n1_S(v321_n);
      nat v323_n = n1_S(v322_n);
      nat v324_n = n1_S(v323_n);
      nat v325_n = n1_S(v324_n);
      nat v326_n = n1_S(v325_n);
      nat v327_n = n1_S(v326_n);
      nat v328_n = n1_S(v327_n);
      nat v329_n = n1_S(v328_n);
      nat v330_n = n1_S(v329_n);
      nat v331_n = n1_S(v330_n);
      nat v332_n = n1_S(v331_n);
      nat v333_n = n1_S(v332_n);
      nat v334_n = n1_S(v333_n);
      nat v335_n = n1_S(v334_n);
      nat v336_right_len = n2_modn(v300_n2, v335_n);
      nat v337_n = n0_O();
      prod_prod_buffer_byteptr_nat
      v338_p
      =
      n4_sse_html_escape2_aligned(v298_buf2,
      v299_ptr2,
      v337_n,
      v318_mid_count);
      prod_buffer_byteptr
      v339_p
      =
      field0_pair_prod_prod_buffer_byteptr_nat(v338_p);
      nat v340_m3 = field1_pair_prod_prod_buffer_byteptr_nat(v338_p);
      buffer v341_buf3 = field0_pair_prod_buffer_byteptr(v339_p);
      byteptr v342_ptr3 = field1_pair_prod_buffer_byteptr(v339_p);
      buffer v343_buf4;
      switch (sw_nat(v340_m3))
      {
        case_O_nat: { v343_buf4 = v341_buf3; break; }
        case_S_nat: {
          nat v344_n = field0_S_nat(v340_m3);
          v343_buf4 = n3_bufaddmem(v341_buf3, v342_ptr3, v340_m3);
          break;
        }
      }
      nat v345_n = n2_subn(v300_n2, v336_right_len);
      byteptr v346_ptr4 = n2_bptradd(v242_ptr, v345_n);
      return n3_trec_html_escape(v343_buf4, v346_ptr4, v336_right_len);
    }
  }
}
