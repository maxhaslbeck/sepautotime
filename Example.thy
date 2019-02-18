theory Example
imports SepLog_Automatic
begin


lemma "<a \<mapsto>\<^sub>a (xs::nat list)  * $3 * \<up> (i < length xs)> 
        do { n \<leftarrow> Array.nth a i;
             m \<leftarrow> Array.nth a i;
             return ( n+m ) }
       <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up> (r = 2 * (xs ! i))>"  
  by (sep_auto simp: zero_time ) 


end