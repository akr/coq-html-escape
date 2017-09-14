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
