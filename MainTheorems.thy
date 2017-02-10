theory MainTheorems
imports TheoremD14
begin

context LocalLexing begin

theorem \<II>_is_generated_by_\<PP>: "\<II> = Gen \<PP>"
proof -
  have "wellformed_items (\<I> (length Doc))"
    using wellformed_items_\<I> by auto
  then have "\<And> x. x \<in> \<I> (length Doc) \<Longrightarrow> item_end x \<le> length Doc"
    using wellformed_item_def wellformed_items_def by blast
  then have "\<I> (length Doc) \<subseteq> items_le (length Doc) (\<I> (length Doc))"
    by (auto simp only: items_le_def)  
  then have "\<I> (length Doc) = items_le (length Doc) (\<I> (length Doc))"
    using items_le_is_filter by blast
  then have \<II>_altdef: "\<II> = items_le (length Doc) (\<I> (length Doc))" using \<II>_def by auto
  have "\<And> p. p \<in> (\<Q> (length Doc)) \<Longrightarrow> charslength p \<le> length Doc"
    using \<PP>_are_doc_tokens \<PP>_def doc_tokens_length by auto
  then have "\<Q> (length Doc) \<subseteq> paths_le (length Doc) (\<Q> (length Doc))"
    by (auto simp only: paths_le_def)
  then have "\<Q> (length Doc) = paths_le (length Doc) (\<Q> (length Doc))"
    using paths_le_is_filter by blast
  then have \<PP>_altdef: "\<PP> = paths_le (length Doc) (\<Q> (length Doc))" using \<PP>_def by auto
  show ?thesis using \<II>_altdef \<PP>_altdef thmD14 by auto
qed

definition finished_item :: "symbol list \<Rightarrow> item"
where
  "finished_item \<alpha> = Item (\<SS>, \<alpha>) (length \<alpha>) 0 (length Doc)"

lemma item_rule_finished_item[simp]: "item_rule (finished_item \<alpha>) = (\<SS>, \<alpha>)"
  by (simp add: finished_item_def)

lemma item_origin_finished_item[simp]: "item_origin (finished_item \<alpha>) = 0"
  by (simp add: finished_item_def)

lemma item_end_finished_item[simp]: "item_end (finished_item \<alpha>) = length Doc"
  by (simp add: finished_item_def)

lemma item_dot_finished_item[simp]: "item_dot (finished_item \<alpha>) = length \<alpha>"
  by (simp add: finished_item_def)

lemma item_rhs_finished_item[simp]: "item_rhs (finished_item \<alpha>) = \<alpha>"
  by (simp add: finished_item_def)

lemma item_\<alpha>_finished_item[simp]: "item_\<alpha> (finished_item \<alpha>) = \<alpha>"
  by (simp add: finished_item_def item_\<alpha>_def)

lemma item_nonterminal_finished_item[simp]: "item_nonterminal (finished_item \<alpha>) = \<SS>"
  by (simp add: finished_item_def item_nonterminal_def)
  
lemma Derives1_of_singleton:
  assumes "Derives1 [N] i r \<alpha>"
  shows "i = 0 \<and> r = (N, \<alpha>)"
proof -
  from assms have "i = 0" using Derives1_bound
    using length_Cons less_Suc0 list.size(3) by fastforce 
  then show ?thesis using assms
    using Derives1_def append_Cons append_self_conv append_self_conv2 length_0_conv 
      list.inject by auto
qed    

theorem Completeness:
  assumes p_in_ll: "p \<in> ll"
  shows "\<exists> \<alpha>. pvalid p (finished_item \<alpha>) \<and> finished_item \<alpha> \<in> \<II>"
proof -
  have p: "p \<in> \<PP> \<and> charslength p = length Doc \<and> terminals p \<in> \<L>"
    using p_in_ll ll_def by auto
  then have derives_p: "derives [\<SS>] (terminals p)"
    using \<L>_def is_derivation_def mem_Collect_eq by blast
  then have "\<exists> D. Derivation [\<SS>] D (terminals p)"
    by (simp add: derives_implies_Derivation)   
  then obtain D where D: "Derivation [\<SS>] D (terminals p)" by blast
  have is_word_p: "is_word (terminals p)"  using leftlang p by blast
  have not_is_word_\<SS>: "\<not> (is_word [\<SS>])" using is_nonterminal_startsymbol is_terminal_nonterminal 
    is_word_cons by blast  
  have "D \<noteq> []" using D is_word_p not_is_word_\<SS> using Derivation.simps(1) by force
  then have "\<exists> d D'. D = d#D'" using D Derivation.elims(2) by blast 
  then obtain d D' where d: "D = d#D'" by blast
  have "\<exists> \<alpha>. Derives1 [\<SS>] (fst d) (snd d) \<alpha> \<and> derives \<alpha> (terminals p)"
    using d D Derivation.simps(2) Derivation_implies_derives by blast 
  then obtain \<alpha> where \<alpha>: "Derives1 [\<SS>] (fst d) (snd d) \<alpha> \<and> derives \<alpha> (terminals p)" by blast
  then have snd_d_in_\<RR>: "snd d \<in> \<RR>" using Derives1_rule by blast 
  with \<alpha> have snd_d: "snd d = (\<SS>, \<alpha>)" using Derives1_of_singleton by blast
  have wellformed_p: "wellformed_tokens p" by (simp add: \<PP>_wellformed p)
  have wellformed_finished_item: "wellformed_item (finished_item \<alpha>)"  
    apply (auto simp add: wellformed_item_def)
    using snd_d snd_d_in_\<RR> by metis    
  have pvalid: "pvalid p (finished_item \<alpha>)" 
    apply (auto simp add: pvalid_def)
    using wellformed_p apply blast
    using wellformed_finished_item apply blast
    apply (rule_tac x="0" in exI)
    apply auto 
    using p apply (simp add: finished_item_def)
    apply (rule_tac x="[]" in exI)
    apply (simp add: is_derivation_def)
    by (simp add: \<alpha>)
  then have "finished_item \<alpha> \<in> Gen \<PP>" using Gen_def mem_Collect_eq p by blast
  then have "finished_item \<alpha> \<in> \<II>" using \<II>_is_generated_by_\<PP> by blast 
  with pvalid show ?thesis by blast
qed

definition PROPER_START :: "bool" where
  "PROPER_START = (\<forall> \<alpha> \<beta>. is_derivation (\<alpha> @ [\<SS>] @ \<beta>) \<longrightarrow> \<alpha> = [] \<or> \<beta> = [])"

definition STRICT_LEXER :: "bool" where
  "STRICT_LEXER = (\<forall> t \<in> \<TT>. 0 \<notin> Lex t Doc 0)"

lemma no_chars_implies_empty_path:
  assumes strict: "STRICT_LEXER"
  assumes p_dom: "p \<in> \<PP>"
  assumes no_chars_p: "chars p = []"
  shows "p = []"
proof -
  {
    assume p_nonempty: "p \<noteq> []"
    with p_dom tokens_nth_in_\<Z> have "\<exists> u. p ! 0 \<in> \<Z> 0 u"
      using charslength.simps charslength_of_prefix is_prefix_take le_0_eq length_greater_0_conv 
        list.size(3) no_chars_p by fastforce
    then have "p ! 0 \<in> \<X> 0" using \<Z>_subset_\<X> by blast  
    then have "\<exists>t l \<omega>. p ! 0 = (t, \<omega>) \<and> t \<in> \<TT> \<and> l \<in> Lex t Doc 0  \<and> \<omega> = take l Doc"
      using \<X>_def by auto
    then obtain t l \<omega> where in_\<X>:
      "p ! 0 = (t, \<omega>) \<and> t \<in> \<TT> \<and> l \<in> Lex t Doc 0 \<and> \<omega> = take l Doc" by blast
    have "is_lexer (Lex t)"
      by (simp add: Lex_is_lexer in_\<X>) 
    with in_\<X> have "l \<le> length Doc" by (metis add.commute add.right_neutral is_lexer_def le0) 
    with in_\<X> have length_\<omega>: "length \<omega> = l" by (simp add: min.absorb2)
    from strict STRICT_LEXER_def in_\<X> have l_nonzero: "l \<noteq> 0" by meson
    have "p = (p ! 0)#(tl p)" using p_nonempty
      by (metis list.exhaust_sel nth_Cons_0) 
    then have "charslength p = length \<omega> + charslength (tl p)" using in_\<X>
      by (metis chars.simps(2) chars_of_token_simp charslength.simps length_append) 
    then have "charslength p \<noteq> 0" using l_nonzero length_\<omega> using add_is_0 by linarith 
    then have "chars p \<noteq> []" by simp
  }
  then show ?thesis using no_chars_p by auto   
qed 

theorem Soundness:
  assumes finished_item_\<alpha>: "finished_item \<alpha> \<in> \<II>"
  assumes condition: "STRICT_LEXER \<or> PROPER_START"
  shows "\<exists> p. pvalid p (finished_item \<alpha>) \<and> p \<in> ll"
proof -
  have "finished_item \<alpha> \<in> Gen \<PP>"
    using \<II>_is_generated_by_\<PP> finished_item_\<alpha> by auto 
  then obtain p where p: "p \<in> \<PP> \<and> pvalid p (finished_item \<alpha>)"
    using Gen_implies_pvalid by blast 
  have pvalid_p_finished_item: "pvalid  p (finished_item \<alpha>)" using p by blast
  from iffD1[OF pvalid_def this, simplified] obtain r \<gamma> where pvalid:
    "wellformed_tokens p \<and>
     wellformed_item (finished_item \<alpha>) \<and>
     r \<le> length p \<and>
     length (chars p) = length Doc \<and>
     chars (take r p) = [] \<and>
     is_derivation (take r (terminals p) @ \<SS> # \<gamma>) \<and> derives \<alpha> (drop r (terminals p))"
     by  blast
  have "item_rule (finished_item \<alpha>) \<in> \<RR>" using pvalid
    using wellformed_item_def by blast
  then have "(\<SS>, \<alpha>) \<in> \<RR>" by simp 
  then have is_derivation_\<alpha>: "is_derivation \<alpha>" by (simp add: is_derivation_def leftderives_rule)
  from condition have "r = 0 \<or> \<gamma> = []"
  proof (induct rule: disjCases2)
    case 1
      have take_r_p_in_\<PP>: "take r p \<in> \<PP>" using is_prefix_take p prefixes_are_paths' by blast
      with no_chars_implies_empty_path have "take r p = []" using pvalid 1 by blast
      with pvalid have "r = 0" using le_0_eq list.size(3) take_eq_Nil by auto 
      then show ?case by blast
  next
    case 2
      note PS = 2
      have "r = 0 \<or> r \<noteq> 0" by arith
      then show ?case
      proof (induct rule:disjCases2)
        case 1 
          then show ?case by blast
      next
        case 2 
          then have take_r_not_empty: "take r (terminals p) \<noteq> []"
            by (metis length_take length_terminals list.size(3) min.absorb2 pvalid)
          with PS pvalid have "\<gamma> = []"
            using PROPER_START_def append_Cons append_Nil by fastforce 
          then show ?case by blast
      qed
  qed
  then have "is_derivation (terminals p)"
  proof (induct rule: disjCases2)
    case 1
      with pvalid have "derives \<alpha> (terminals p)" by simp
      then show ?case using is_derivation_\<alpha> using derives_trans is_derivation_def by blast 
  next
    case 2
      with pvalid have "is_derivation (take r (terminals p) @ [\<SS>])" by simp
      then have "is_derivation (take r (terminals p) @ \<alpha>)" using is_derivation_\<alpha>
        append_Nil2 is_derivation_def is_derivation_derives by force
      then have "is_derivation (take r (terminals p) @ (drop r (terminals p)))" 
        by (metis append_Nil2 pvalid is_derivation_derives)
      then show "is_derivation (terminals p)" by simp 
  qed  
  then have "p \<in> ll"
    by (simp add: \<L>_def is_word_terminals ll_def p pvalid)       
  with pvalid_p_finished_item show ?thesis by auto
qed

lemma is_finished_and_finished_item:
  assumes wellformed_x: "wellformed_item x"
  shows "is_finished x = (\<exists> \<alpha>. x = finished_item \<alpha>)"
proof -
  {
    assume is_finished_x: "is_finished x"
    obtain \<alpha> where \<alpha>: "\<alpha> = item_rhs x" by blast
    have "x = finished_item \<alpha>"
      apply (rule item.expand)
      apply auto
      using \<alpha> is_finished_def is_finished_x item_nonterminal_def item_rhs_def apply auto[1]
      using \<alpha> assms is_complete_def is_finished_def is_finished_x wellformed_item_def apply auto[1]
      using is_finished_def is_finished_x apply blast
      using is_finished_def is_finished_x by auto
    then have "\<exists> \<alpha>. x = finished_item \<alpha>" by blast
  }
  note left_implies_right = this
  {
    assume "\<exists> \<alpha>. x = finished_item \<alpha>"
    then obtain \<alpha> where \<alpha>: "x = finished_item \<alpha>" by blast
    have "is_finished x" by (simp add: \<alpha> is_finished_def is_complete_def)
  }
  note right_implies_left = this
  show ?thesis using left_implies_right right_implies_left by blast
qed 

theorem Correctness:
  assumes "STRICT_LEXER \<or> PROPER_START"
  shows "(ll \<noteq> {}) = earley_recognised"
proof -
  have 1: "(ll \<noteq> {}) = (\<exists> \<alpha>. finished_item \<alpha> \<in> \<II>)"
    using Soundness Completeness assms ex_in_conv by fastforce
  have 2: "(\<exists> \<alpha>. finished_item \<alpha> \<in> \<II>) = (\<exists> x \<in> \<II>. is_finished x)"
    using \<II>_def is_finished_and_finished_item wellformed_items_\<I> wellformed_items_def by auto
  show ?thesis using earley_recognised_def 1 2 by blast
qed 

end

end