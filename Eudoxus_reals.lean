import data.int.basic
import tactic
import group_theory.quotient_group
import init.data.nat.lemmas
import init.data.int.basic
import data.set.finite
import algebra.archimedean
import order.conditionally_complete_lattice
import data.real.basic

open set

def df (f : ℤ → ℤ) : ℤ → ℤ → ℤ := λ p q, f (p + q) - f p - f q

def almost_homomorphism (f : ℤ → ℤ) : Prop :=  ∃ (C : ℤ),∀ (p q : ℤ),abs(df f p q) < C
 
def G := ℤ → ℤ 
instance : has_add G := ⟨λ f g, λ z, f z + g z⟩
instance : add_group G :=  
{add := λ f g, λ z, (f z + g z),
 add_assoc := begin intros f g h, simp only [], ext1, exact add_assoc (f x) (g x) (h x) end,
 zero := λ z, 0,
 zero_add := begin intro f, ext1, tidy, end,
 add_zero := begin intro f, ext1, tidy, end,
 neg := λ f, λ z, - f z,
 add_left_neg := begin intro f, ext1, tidy, end}

def S : add_subgroup G :=  
{ carrier := {f : ℤ → ℤ | almost_homomorphism f},
  zero_mem' := begin use 5, intros p q, tidy end,
  add_mem' := 
  begin 
    intros a b ha hb, 
    rcases ha with ⟨C, hC⟩, 
    rcases hb with ⟨D, hD⟩, 
    use C + D,
    intros p q,
    specialize hC p q,
    specialize hD p q,
    have h : ∀ (f g : G)(z : ℤ), (f + g) z = f z + g z, 
      tidy,
    rw abs_lt at *,
    cases hC, cases hD,
    simp [df] at *,
    fsplit,
    linarith,
    linarith,
  end,
  neg_mem' := 
  begin
    intros f hf,
    rcases hf with ⟨C, hC⟩,
    use C,
    intros p q,
    specialize hC p q,
    rw df at *,
    tidy,
    have h : ∀ z : ℤ, (- f) z = - f z,
     tidy,
    rw abs_lt at *,
    cases hC,
    split,
      linarith,
      linarith
  end}

def B : add_subgroup S := 
 {carrier := {f : S | ∃ (B : ℤ), ∀ (x : ℤ), abs(f.1 x) ≤ B},
  zero_mem' := begin use 5, intro x, tidy end,
  add_mem' := 
  begin 
    intros f g, 
    intros hf hg,
    rcases hf with ⟨B, hB⟩, 
    rcases hg with ⟨C, hC⟩,
    use B + C,
    intro x,
    specialize hC x,
    specialize hB x,
    have h1 : ∀ (f g : S) (x : ℤ), (f + g).1 x = f.1 x + g.1 x, 
      intros f g x,
      refl,
    rw h1, 
    rw abs_le at *,
    cases hC, 
    cases hB,
    split,
      simp only [neg_add_rev],
      linarith,
      linarith,
  end,
  neg_mem' := 
  begin 
    intros f hf,
    rcases hf with ⟨B, hB⟩,
    use B,
    intro x,
    specialize hB x,
    have h : ∀ (f : S)(x : ℤ), (- f).1 x = - f.1 x,
      intros f x,
      refl,
    rw h,
    rw abs_neg, 
    exact hB 
  end}

instance add_comm_G : add_comm_group G := 
{ add_comm:= 
  begin 
    intros f g, 
    tidy, 
  have h:∀ (f g : G)(z : ℤ), (f + g) z = f z + g z, 
    tidy, 
  exact add_comm (f x) (g x), 
  end,
  ..G.add_group}

def 𝔼  := quotient_add_group.quotient B  

instance : add_comm_group 𝔼 := quotient_add_group.add_comm_group B  

instance : has_lift_t ℤ ℕ := ⟨sizeof⟩ 

lemma l1 {f : ℤ → ℤ}(hf : almost_homomorphism f)(hf2 : ∀ n > 0, ∃ m > 0, f m > n) : 
∀ D > 0 , ∃ M > 0 , ∀ m > 0, f (m * M) > (m + 1) * D := 
begin
 intros D hD,
 rcases hf with ⟨C, hC⟩,
 have h : C > 0,
  specialize hC 1 2,
  have h2 : 0 ≤ abs(df f 1 2) ,
   apply abs_nonneg,
  linarith,
 let E := (D + C),
   have h3 : E = D + C,
   refl,
  have hE : E > 0,
   rw h3,
   linarith,  
 specialize hf2 (2 * E),
 have h2E : 2 * E > 0,
  norm_num,
  exact hE,
 rcases hf2 h2E with ⟨M, hM, hME⟩, 
 use [M, hM],
 intros m hm,
 induction m with k hk,
 have h4 : f M > 2 * D,
  have h5 : E > D,
   rw h3,
   exact lt_add_of_pos_right D h,
 linarith,
 {induction k with k hk,
   {exfalso,
  tidy},
 {cases k with hk1 hkn,
   {simp,
   linarith},
   simp at hk ⊢ hm,
   by_cases int.of_nat hk1 + 1 > 0,
    have h7 :  f (↑(hk1.succ) * M) > (↑(hk1.succ) + 1) * D,
     apply hk,
    have h8 : f (↑(hk1.succ.succ) * M) = f (↑(hk1.succ) * M) + f (M) + df f (↑(hk1.succ) * M) M,
     have h9 : ↑(hk1.succ + 1) * M = (↑(hk1.succ) +1) * M,
      refl,   
     rw h9,
     simp only [add_mul],
     rw df,
     simp,
    simp at h8,
    rw h8,
    have h10 : df f (↑(hk1.succ) * M) M > -E,
     specialize hC (↑(hk1.succ) * M) M,
     rw abs_lt at hC, 
     have h11 : -E < -C,
      rw h3,
      linarith,
     linarith,
    have h12 : f (↑(hk1.succ) * M) + f (M) + df f (↑(hk1.succ) * M) M 
    > (↑(hk1.succ) + 1) * D + 2 * E - E,
      linarith,
    have h13 : (↑(hk1.succ) + 1) * D + (2 * E - E) > (↑(hk1.succ.succ) + 1) * D,
     simp only [gt_iff_lt],
     have h14 : 2 * E + (-1) * E = E,
      rw ←add_mul,
      norm_num,
     have h15 : - E = (-1) * E,
      norm_num,
     rw ←h15 at h14,
     rw ←sub_eq_add_neg at h14,
     rw h14, 
     have h16 : (↑(hk1.succ) + 1) * D + E > (↑(hk1.succ) + 1) * D + 1 * D,
      simp,
      linarith,
     rw ←add_mul at h16,
     have  h17 : (↑(hk1.succ) + 1 + 1) * D = (↑(hk1.succ.succ) + 1) * D,
      refl,
     rw h17 at h16,
     linarith,
    simp at h13 h12,
    linarith,
    simp only [gt_iff_lt, int.succ_coe_nat_pos,←not_le,not_not] at h,
    have hm1 : 0  + 1 < int.of_nat hk1 + 1 + 1 + 1,
      simp,
      linarith,
    have hm2 : 1 ≤ int.of_nat hk1 + 1 + 1,
     exact int.lt_add_one_iff.mp hm1,
    simp at hm2,
    have hm0 : int.of_nat hk1 + 1 = 0,
     exact le_antisymm h hm2,
    rw int.coe_nat_eq,
    rw hm0,
    ring_nf,
    exact h4}},
   {exfalso,
   tidy},
end

instance has_zero_G (G : Type)[add_comm_group G] : has_zero G := add_zero_class.to_has_zero G
instance has_add_G (G : Type)[add_comm_group G] : has_add G := add_semigroup.to_has_add G
instance has_neg_G (G : Type)[add_comm_group G] : has_neg G := sub_neg_monoid.to_has_neg G

structure ordered_abelian_group (G : Type) [add_comm_group G]:=
(P : set G)
(positive : (0 : G) ∉ P)
(add_mem' : ∀ a b : G, a ∈ P → b ∈ P → a + b ∈ P)
(pos_mem : ∀ x : G, x ≠ 0 → (x ∈ P ∧ -x ∉ P) ∨ (-x ∈ P ∧ x ∉ P))

noncomputable instance oag_is_total_ordered (X : Type)[add_comm_group X](G : ordered_abelian_group X) : linear_order X :=
begin
 refine
 {lt := λ a b, b - a ∈ G.P,
 le := λ a b, b - a ∈ G.P ∨ b = a,
 decidable_le := begin exact classical.dec_rel (λ a b, b - a ∈ G.P ∨ b = a) end,
 le_refl := begin intro a, simp end,
 le_trans := begin intros a b c hab hbc, 
 simp at *, 
 cases hab, 
 cases hbc, 
  {have h : b -a + (c- b) ∈ G.P, 
   apply G.add_mem' (b-a) (c -b), 
   exact hab, 
   exact hbc, 
   have h2 : b + -a + (c + -b) = c - a, 
    rw add_comm,
    rw add_assoc, 
    have h3 : -b + (b + -a) = -b + b + -a, 
     rw ←add_assoc,
     rw h3, 
     norm_num, 
     exact tactic.ring.add_neg_eq_sub c a,
   have h4 : b + -a + (c + -b) = b - a + (c - b), 
    ring_nf,
   rw h4 at h2, 
   rw h2 at h,
   apply or.intro_left,
   exact h},
   {rw ←hbc at hab,
   apply or.intro_left,
   exact hab},
   {rw hab at hbc,
    exact hbc}       
   end,
 lt_iff_le_not_le := 
 begin 
  intros a b,
  split,
  {intro hab,
  simp at *, 
   split,
   apply or.intro_left,
   exact hab,
   have hab0 : ¬a - b = 0,
    by_contradiction,
    have hab0' : a = b,
      have x: a - b + b = 0 + b,
        exact congr_fun (congr_arg has_add.add h) b,
      simp at x,
      exact x,
    rw hab0' at hab,
    simp at hab,
    exact G.positive hab,
   rw push_neg.not_eq  at hab0,
   have hf : (a-b ∈ G.P ∧ -(a - b) ∉ G.P) ∨ (-(a - b) ∈ G.P ∧ a - b ∉ G.P),
    apply G.pos_mem (a-b) hab0,
   simp at hf,
   cases hf,
    cases hf,
    by_contradiction,
    exact hf_right hab,
    cases hf,
    by_contradiction,
    cases h,
    exact hf_right h,
    rw h at hab,
    simp at hab,
    exact G.positive hab},
  {rintro ⟨hab, hnba⟩,
   simp at *,
   tidy}
 end,
 le_antisymm := 
 begin
  intros a b,
  intros hba hab,
  tidy,
  have h : ¬¬(a - b = 0),
   by_contradiction,
   rw push_neg.not_eq at h,
   have hf : (a-b ∈ G.P ∧ -(a - b) ∉ G.P) ∨ (-(a - b) ∈ G.P ∧ a - b ∉ G.P),
    apply G.pos_mem (a-b) h,
   simp at hf,
   cases hf,
    cases hf,
    exact hf_right hba,
    cases hf,
    exact hf_right hab,
    simp at h,
    exact sub_eq_zero.mp h
 end,
 le_total :=
  begin   
   intros a b,
   by_cases (a = b),
    tidy,
   rw push_neg.not_eq at h,
   have h2 : a - b ≠ 0,
    exact sub_ne_zero.mpr h,
   have hf : (a-b ∈ G.P ∧ -(a - b) ∉ G.P) ∨ (-(a - b) ∈ G.P ∧ a - b ∉ G.P),
    apply G.pos_mem (a-b) h2,
   cases hf,
    {cases hf,
    apply or.intro_right,
    apply or.intro_left,
    exact hf_left},
    {cases hf,
     simp at hf_left,
     apply or.intro_left,
     apply or.intro_left,
     exact hf_left}
  end}, 
end

lemma l2 (f : ℤ → ℤ) : ∀ M N, ∃ B, ∀ n : ℤ , N ≤ n ∧ n < M → 
abs(f n) < B :=
begin
  intros M N,
  let I := {n : ℤ | N ≤ n ∧ n < M},
  have h1 : finite I :=
    ⟨fintype.of_finset (finset.Ico N M) (by { simp [int.add_one_le_iff] })⟩,
  have h2 : bdd_above (f '' I) := finite.bdd_above (finite.image f h1),
  have h3 : bdd_below (f '' I) := finite.bdd_below (finite.image f h1),
  rcases h2 with ⟨B1, hB1⟩,
  rcases h3 with ⟨B2, hB2⟩,
  use (max (abs(B1)) (abs(B2)) + 1), 
  rintros n hn,
  have hnI : n ∈ I := hn, 
  rw mem_upper_bounds at hB1,
  rw mem_lower_bounds at hB2,
  specialize hB1 (f n) (mem_image_of_mem f hnI),
  specialize hB2 (f n) (mem_image_of_mem f hnI),
  rw abs_lt,
  split,
   {have h5 : B2 > -(max (abs(B1)) (abs(B2))+ 1),
    calc B2 >= -abs(-B2) : neg_le.mp (le_abs_self (-B2))
        ... =  -abs(B2) : by simp
        ... >= -(max  (abs(B1)) (abs(B2))) : neg_le_neg_iff.mpr (le_max_right _ _)
        ... > -(max  (abs(B1)) (abs(B2)) + 1) : by linarith,
     linarith},
   {have h4 : B1 <  max (abs(B1)) (abs(B2)) + 1,
    calc B1 ≤ abs(B1) : le_abs_self _
       ... ≤ max  (abs(B1)) (abs(B2)) : le_max_left (abs(B1)) (abs(B2))
       ... < max (abs(B1)) (abs(B2)) + 1 : by linarith,
    linarith}
end
/- intros M hM,
 induction M with m hm,
 {induction m with m hm,
 {use 0,
 simp},
 {by_cases int.of_nat m > 0, 
   have hm :  ∃ B, ∀ n : ℤ ,0 ≤ n ∧ n < int.of_nat m → abs(f n) < B,
    apply hm h,
   rcases hm with ⟨B', hB'⟩,
 let B := max B' (abs(f m)+1),
 use B,
 intros n hn,
 cases hn with hn1 hn2,
 by_cases hmn : n < m,
  specialize hB' n,
  have hB'2 : abs(f n) < B',
   apply hB' (and.intro hn1 hmn),
  linarith [hB'2, (le_max_left B' (abs(f ↑m)+1))],
  rw not_lt at hmn,
  have h : n ≤ m,
   simp at hn2,
   exact int.lt_add_one_iff.mp hn2,
  have h2 : n = m,
   exact le_antisymm h hmn,
  rw h2,
  have h3 : abs(f ↑m) +1 ≤ B,
   exact le_max_right B' (abs(f ↑m) + 1),
  have h4 : abs(f ↑m) < abs(f ↑m) + 1,
   exact lt_add_one (abs(f ↑m)),
  linarith,
   simp at h,
   use (abs(f 0) + 1),
   intro n,
   rw h,
   simp,
   intros hn1 hn2,
   have hn' : n < 0 + 1,
    linarith,
   have hn2 : n ≤ 0,
    apply int.lt_add_one_iff.mp hn',
   have hn0 : n = 0,
    exact le_antisymm hn2 hn1,
   rw hn0,
   linarith}},
  {exfalso,
  tidy}
end-/

instance : has_sub G := sub_neg_monoid.to_has_sub G
instance has_sub_Z_Z : has_sub (ℤ → ℤ) := G.has_sub

lemma l3 (f : ℤ → ℤ)(x y : ℤ) : f (x + y) = f x + f y + df f x y :=
 begin
  rw df,
  tidy,
 end

lemma l5  (A B C : ℤ) : A > 0 →  B > 0 → C > 0 → ∃ n > 0 ,
(n + 1) * A > B + C:=
begin
  intros hA hB hC,
  have h1 : (B + C) > 0,
   exact add_pos hB hC,
 use [(B + C),h1],
 have hA1 : A >= 1,
  exact int.add_one_le_of_lt hA,
 have hBC : B + C +1 > B + C,
  linarith,
 have hf : (B + C) ≤ (B + C ) * A ,
  exact (le_mul_iff_one_le_right h1).mpr hA1,
 have h3 :(B + C) * A < (B + C + 1) * A,
  exact (mul_lt_mul_right hA).mpr hBC,
 linarith
end

lemma l6 {f : ℤ → ℤ} (hf : almost_homomorphism f) : (∀ B > 0, ∃ m > 0, f m > B) → 
∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f p > C := 
begin
 intro hp,
 have  hl1 : ∀ D > 0 , ∃ M > 0 , ∀ m > 0,  f (m * M) > (m + 1) * D,
     exact l1 hf hp,
    rcases hf with ⟨D, hD⟩,
    have hDp : D > 0,
     specialize hD 0 1,
     have h1 : abs(df f 0 1) >= 0,
      exact abs_nonneg (df f 0 1),
    linarith,
    specialize hl1 D hDp,
    rcases hl1 with ⟨M,hM,hl1⟩, 
    let g : ℤ → ℤ := λ p, f(p - (p % M)),
    have h :∀ p, p = p % M + M * (p / M),
     intro p,
     exact (int.mod_add_div p M).symm,
    have h2 : ∃ B, ∀ n : ℤ ,0 ≤ n ∧ n < M → abs(f n) < B,
      apply l2 f M 0,
    rcases h2 with ⟨E, hE⟩,
    have hfg : ∃ B : ℤ, ∀ p, abs((f - g) p) < B, 
      let B := E + D,
       use B,
       intro p,
      have hBED : B = E + D,
       refl,
     let d := p / M,
     let r := p % M, 
     specialize h p,
     have h3 : p = d * M + r,
      rw h,
      ring,
     have h4 : g p = f (d * M),
      have h5 : g p = f (p - p % M),
       refl,
      have h6 : d * M = p - p % M,
       have h7 : r = p % M,
        refl,
       rw ←h7,
       rw h3,
       simp,
      rw h6,
     have h8: abs(f r) < E, 
       have h9 : r < M,
        exact int.mod_lt_of_pos p hM,
       have hr0 : 0 ≤ r,
        exact int.mod_nonneg p (ne_of_gt hM),
       specialize hE r,
      apply hE (and.intro hr0 h9),
     specialize hD (d * M) r, 
     calc abs((f - g) p) 
           = abs((f - g) (p % M + M * (p / M))) : by rw ←h
        ...= abs((f - g) ( r + M * d)) : by simp
        ...= abs((f - g) ( d * M + r)) : by {rw add_comm, rw mul_comm} 
        ...= abs(f (d * M + r) - g (d * M + r)) : by ring
        ...= abs(f (d * M) + f r + (df f (d * M) r) - g ( d* M + r)) : by rw l3 f (d * M) r
        ...= abs(f (d * M) + f r + (df f (d * M) r) - g p) : by rw ←h3
        ...= abs(f (d * M) + f r + (df f (d * M) r) - f (d * M)) : by rw ←h4
        ...= abs(f r + (df f (d * M) r)) : by ring_nf
        ...≤ abs(f r) + abs(df f (d * M) r) : by apply abs_add
        ...< E + D : by linarith
        ...= B : rfl,
     intros C hC,
     rcases hfg with ⟨B, hB⟩,
     have hBp : B > 0,
      specialize hB 1,
      linarith [abs_nonneg ((f - g) 1)],
     have lb :  ∃ n > 0 ,(n + 1) * D > B + C,
      apply l5 D B C hDp hBp hC,
     rcases lb with ⟨n, hn0, hn⟩,
     let N := n * M,
     have hN : N = n * M,
      refl,
     use N,
     intros p hp,
     let d := p / M,
     let r := p % M, 
     have h2 : p = d * M + r,
      specialize h p,
      rw h,
      ring,
     have hg : g p = f (d * M),
      have h5 : g p = f (p - p % M),
       refl,
      have h6 : d * M = p - p % M,
       have h7 : r = p % M,
        refl,
       rw ←h7,
       rw h2,
       simp,
      rw h6,
     have hd : n ≤ d,
      simp only [h2,hN] at hp,
      have h3 : d * M + M > d * M + r,
       have hMr : M > r,
        exact int.mod_lt_of_pos p hM, 
      linarith,
      have h4 : (d + 1) * M > n * M,
       rw add_mul,
       linarith,
      have h5 : d + 1 > n,
       exact (mul_lt_mul_right hM).mp h4, 
     exact int.lt_add_one_iff.mp h5,
     have hd0 : d > 0,
      linarith,
     have h6 : (d + 1) * D >= (n + 1) * D,
      have h7 : d + 1 >= n + 1,
       linarith,
     exact (mul_le_mul_right hDp).mpr h7,      
     specialize hl1 d hd0,
     have hgBC : g(p) > B + C,
      calc g(p) = f(d * M) : by rw hg
            ... > (d + 1) * D : by apply hl1
            ...>= (n + 1) * D : by apply h6
            ... > B + C : by apply hn,
     specialize hB p,
     rw abs_lt at hB,
     cases hB with hB _,
     have hg : f p - g p = (f - g) p,
      refl,
     rw ←hg at hB,
     have hf' : f p - g p + g p > - B + g p,
      exact add_lt_add_right hB (g p),
     calc f p > - B + g p: by {simp only [sub_add_cancel, neg_add_lt_iff_lt_add] at hf',exact hf'}
          ... > - B + (B + C) : by linarith
          ... = C : by ring,
end

instance : has_neg G := has_neg_G G
instance has_neg_Z_Z : has_neg (ℤ → ℤ) := G.has_neg
instance has_add_Z_Z : has_add (ℤ → ℤ) := G.has_add

@[simp] lemma l7 (f : ℤ → ℤ)(x : ℤ) : (-f) x = -f x := begin tidy, end

@[simp] lemma l8 (f g : ℤ → ℤ)(x : ℤ) : (f + g) x = f x + g x := begin tidy, end

lemma l9 {f : ℤ → ℤ} (hf : almost_homomorphism f) : (∃ B : ℤ, ∀ x : ℤ, abs (f x) ≤ B) 
∨ (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f p > C) ∨ ∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f p < -C := 
begin
 by_cases (∀ B > 0, ∃ m > 0, f m > B) ∨ (∀ B > 0, ∃ m > 0, f m < -B),
 { cases h with hp hn,
   {apply or.intro_right,
    apply or.intro_left,
    exact l6 hf hp},
   {apply or.intro_right,
    apply or.intro_right,
    let g := -f,
    have hgf : g = -f,
     refl,
    have hfS : f ∈ S,
     exact hf,
    have hgS : g ∈ S,
     exact S.neg_mem hfS,
    have hng : ∀ B > 0, ∃ m > 0, g m > B,
     intros B hB,
     specialize hn B hB,
     rcases hn with ⟨m, hm, hmB⟩,
     use [m, hm], 
     rw hgf,
     rw l7,
     exact lt_neg.mp hmB,
    have hg : ∀ C > 0, ∃ N : ℤ, ∀ p, p > N → g p > C,
     exact l6 hgS hng,
    intros C hC,
    specialize hg C hC,
    rcases hg with ⟨N, hN⟩,
    use N,
    intros p hp,
    specialize hN p hp,
    rw hgf at hN,
    rw l7 at hN,  
    exact lt_neg.mp hN}},  
 {rw not_or_distrib at h,
 rw not_forall at h,
 rw not_forall at h,
 cases h,
 rcases h_left with ⟨B1, hB1⟩,
 rcases h_right with ⟨B2, hB2⟩,
 apply or.intro_left,
 rcases hf with ⟨B3, hB3⟩,
 let B := max B1 B2,
 let B' := max B (abs(f 0)),
 have hBB' : B ≤ B',
    exact le_max_left B (abs (f 0)),
 let Bmax := B' + B3 + abs(f 0),
 use Bmax,
 intro x,
 have hp : ∀ y : ℤ, y > 0 → abs (f y) ≤  B',
   intros y hy,
   rw not_imp at hB1 hB2,
   cases hB1 with hB1p hB1,
   cases hB2 with hB2p hB2,
   rw not_exists at hB1 hB2,
   specialize hB1 y,
   specialize hB2 y,
   rw not_exists at hB1 hB2,
   have h1 : ¬f y < -B2,
    exact hB2 hy,
   rw not_lt at h1,
   have h2 : f y >= -B',
    have h2' : f y >= -B,
     have h2'' : B2 ≤ B,
      exact le_max_right B1 B2,
     have h25 : -B2 >= -B,
      exact neg_le_neg h2'',
     linarith,
    have hBB'2 : -B >= -B',
      exact neg_le_neg hBB',
   linarith,
 rw abs_le,
 split,
  exact h2,
  have h3 : ¬f y > B1,
   exact hB1 hy,
  have h3' : f y ≤ B1,
   exact not_lt.mp (hB1 hy),
  have h4 : B1 ≤ B,
   exact le_max_left B1 B2,
  linarith,
 by_cases hx : x > 0,
  { specialize hp x,
    have h2'' : B' ≤ Bmax,
    change B' ≤ B' + B3 + abs(f 0),
    have hB3p : B3 >= 0,
     specialize hB3 0 1,
     have h01 : abs (df f 0 1) >= 0,
      exact abs_nonneg (df f 0 1),
     linarith,
     have hf0 : abs(f 0) >= 0,
      exact abs_nonneg (f 0),
    linarith,
    have h3 :  abs (f x) ≤  B',
     apply hp hx,
 linarith},
 {simp at hx,
  specialize hB3 (-x) x,
  have h1 : f(x) = f(0) - f(-x) - df f (-x) x,
   rw df,
   simp,
  rw h1,
  have h2 : abs((f 0) -f(-x) - df f (-x) x) ≤ abs(f 0) + abs(-f(-x)) + abs(-df f (-x) x),
    exact abs_add_three (f 0) (-(f (-x))) (-df f (-x) x),
  have h3: abs(f 0) + abs(-f(-x)) + abs(-df f (-x) x) < Bmax,
   change abs(f 0) + abs(-f(-x)) + abs(-df f (-x) x) < B' + B3 + abs(f 0),
   have h4 : abs(-f(-x)) ≤ B',
    rw abs_neg,
    by_cases x = 0,
     {rw h,
     simp},
     {have hx2 :x < 0,
     exact lt_of_le_of_ne hx h,
    have hx3 : -x > 0,
     exact neg_pos.mpr hx2,
    specialize hp (-x),
    exact hp hx3},
  rw abs_neg at *,
  rw abs_neg at *, 
  linarith,
  linarith}}
end

lemma l9_exclusive_12 {f : ℤ → ℤ} (hf : almost_homomorphism f) : 
(∃ B : ℤ, ∀ x : ℤ, abs (f x) ≤ B) → (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f p > C) → false :=
begin  
 intros h1 h2,
 rcases h1 with ⟨B ,hB⟩,
 have hB2 : B >= 0,
  specialize hB 1,
  linarith[abs_nonneg (f 1)],
  by_cases B > 0,
   {specialize h2 B h,
   rcases h2 with ⟨N, hN⟩,
   specialize hB (N + 1),
   have hN1 : N + 1 > N,
    linarith, 
   specialize hN (N + 1) hN1,
   rw abs_le at hB,
   cases hB,
   linarith},
   {simp at h,
    have hB0 : B = 0,
     exact le_antisymm h hB2,
     have hn2 : ¬ (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f p > C),
      simp,
      use 1,
      split,
       norm_num,
       intros N,
       use N + 1,
       split,
        linarith,
        specialize hB (N + 1),
        rw [hB0, abs_le] at hB,
        cases hB,
        linarith,
    exact hn2 h2}
end

lemma l9_exclusive_13 {f : ℤ → ℤ} (hf : almost_homomorphism f) : 
(∃ B : ℤ, ∀ x : ℤ, abs (f x) ≤ B) → (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f p < -C) → false :=
begin
  intros h1 h2,
  let g := -f,
  have hgf : g = -f,
   refl,
  have hfS : f ∈ S,
   exact hf,
  have hgS : g ∈ S,
    exact S.neg_mem hfS,
  have hg1 : ∃ B : ℤ, ∀ x : ℤ, abs (g x) ≤ B,
    rcases h1 with ⟨B, hB⟩,
    use B,
    intro x,
    specialize hB x,
    rw [hgf,l7],
    simp,
    exact hB,
  have hg2 : (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → g p > C),
    intros C hC,
    specialize h2 C hC,
    rcases h2 with ⟨N, hN⟩,
    use N,
    intros p hp,
    specialize hN p hp,
    rw [hgf,l7],
    exact lt_neg.mp hN,
  exact l9_exclusive_12 hgS hg1 hg2
end

lemma l9_exclusive_23 {f : ℤ → ℤ} (hf : almost_homomorphism f) :
(∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f p > C) → (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f p < -C) → false :=
begin
  intros h1 h2,
  have h35 : @gt int int.has_lt 35 0,
   norm_num,
  specialize h1 35 h35,
  specialize h2 35 h35,
  rcases h1 with ⟨N, hN⟩,
  rcases h2 with ⟨N', hN'⟩,
  let M := (max N N') + 1,
  have hM : M = (max N N') + 1, refl,
  have hNN'M : M > max N N',
    rw hM,
    linarith,  
  have hNM : M > N,
    linarith[le_max_left N N'],
  have hN'M : M > N',
    linarith[le_max_right N N'],
  specialize hN M hNM,
  specialize hN' M hN'M,
  linarith,
end

instance : has_coe_t S 𝔼  := ⟨quotient_add_group.mk⟩ 
instance : has_lift_t S 𝔼 := coe_to_lift

lemma l10 {f : 𝔼} {f' : S}(hf' : ↑f' = f) : 
-f ∈ {f : 𝔼 | ∃ (f' : S)(h :  ↑f' = f), ∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f'.1 p > C} ↔  
 (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f'.1 p < -C) :=
begin
  split,
  {intro h,
  rcases h with ⟨f'', hff'', hf''⟩,
  have h2 : -↑f'' = f,
    exact neg_eq_iff_neg_eq.mp (eq.symm hff''),
  rw ←quotient_add_group.coe_neg at h2,
  rw ←hf' at h2,
  rw quotient_add_group.eq at h2,
  rcases h2 with ⟨B , hB⟩, 
  intros C hC,
  have hBC : B + C > 0,
    have hD' : B >= 0,
      specialize hB 5,
      linarith [abs_nonneg ((- -f'' + f').1 5)],
    linarith,
  specialize hf'' (B + C) hBC,
  rcases hf'' with ⟨N, hN⟩,
  use N,
  intros x hx,
  specialize hB x,
  specialize hN x hx,
  simp only [add_subgroup.coe_add, neg_neg, subtype.val_eq_coe] at hB,
  rw l8 at hB,
  rw abs_le at hB,
  rw ←subtype.val_eq_coe at hB,
  rw ←subtype.val_eq_coe at hB,
  cases hB with hB1 hB2,
  rw add_comm at hB2,
  have h4 : B  < f''.1 x -C,
    exact lt_sub_iff_add_lt.mpr hN,
  have h5 : B - f''.1 x < f''.1 x - C -f''.1 x,
    exact sub_lt_sub_right h4 (f''.val x),
  simp at h5,
  ring_nf,
  calc f'.1 x ≤ B  - f''.1 x : by exact le_sub_iff_add_le.mpr hB2
          ... < -C : by exact h5},
  {intro h,
  use -f',
  split,
    simp[hf'],
    intros C hC,
    specialize h C hC,
    rcases h with ⟨N, hN⟩,
    use N,
    intros p hpN,
    specialize hN p hpN,
    simp at *,
    linarith}
end

lemma l11 {f : 𝔼}{f' : S}(hf' : ↑f' = f) :
f ∈ {f : 𝔼 | ∃ (f' : S)(h :  ↑f' = f), ∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f'.1 p > C} →  
 (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f'.1 p > C) :=
begin
  intro h,
  rcases h with ⟨f'', hff'', hf''⟩,
  rw ←hff'' at hf',
  rw quotient_add_group.eq at hf',
  rcases hf' with ⟨B, hB⟩,
  intros C hC,
  have hBC : B + C > 0,
    have hD' : B >= 0,
      specialize hB 5,
      linarith [abs_nonneg ((-f' + f'').1 5)],
    linarith,
  specialize hf'' (B + C) hBC,
  cases hf'' with N hN,
  use N,
  intros p hp,
  specialize hN p hp,
  specialize hB p,
  simp at hB,
  rw abs_le at hB,
  rw ←subtype.val_eq_coe at hB,
  rw ←subtype.val_eq_coe at hB,
  cases hB with hB1 hB2,
  linarith
end

def E' : ordered_abelian_group 𝔼 := 
begin
  refine 
  {P := {f : 𝔼 | ∃ (f' : S)(h :  ↑f' = f), ∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f'.1 p > C}, 
  positive :=
  begin 
    by_contradiction,
    rcases h with ⟨a, ha,h⟩,
    have h00 : ↑(0 : S) = (0 : 𝔼),
      apply quotient_add_group.coe_zero,
    rw ←h00 at ha,
    rw quotient_add_group.eq at ha,
    simp at ha,
    exact l9_exclusive_12 a.2 ha h 
  end, 
  add_mem' := 
  begin
    intros f g hf hg,
    rcases hf with ⟨f', hff', hf'⟩,
    rcases hg with ⟨g', hgg', hg' ⟩,  
    use (f' + g'),
    split,
    rw quotient_add_group.coe_add,
    rw [hff',hgg'],
    intros C hC,
    specialize hf' C hC,
    specialize hg' C hC,
    rcases hf' with ⟨N, hN⟩,
    rcases hg' with ⟨N', hN'⟩,
    let M := (max N N') + 1,
    have hM : M = (max N N') + 1, refl,
    have hNN'M : M > max N N',
      rw hM,
      linarith,  
    have hNM : M > N,
      linarith[le_max_left N N'],
    have hN'M : M > N',
      linarith[le_max_right N N'],
    use M,
    intros p hp,
    have hpN : p > N,
      linarith,
    have hpN' : p > N',
      linarith,
    specialize hN p hpN,
    specialize hN' p hpN',
    simp at *,
    linarith
  end, 
 pos_mem := 
 begin
  intros f hf0,
  have h : ∀ f : 𝔼, ∃ f' : S, ↑f' = f,
    exact quot.exists_rep,
  specialize h f,
  rcases h with ⟨f', hf'⟩,
  have h1 : (∃ B : ℤ, ∀ x : ℤ, abs (f'.1 x) ≤ B)  ∨ (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f'.1 p > C) 
  ∨ (∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f'.1 p < -C),
    exact l9 f'.2,
  cases h1 with hf hpn,
  {exfalso,
    have hf'B : f' ∈ B,
      exact hf,
    have hf'B0 :  - 0 + f' ∈ B,
      simp,
      exact hf'B,
    rw ←quotient_add_group.eq at hf'B0,
    rw ←hf'B0 at hf',
    simp at hf',
    exact hf0 hf'.symm},
  {cases hpn with hp hn,
    {apply or.intro_left,
    split,
      use [f', hf'],
      exact hp,
      by_contradiction,
      have hn : ∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f'.1 p < -C,
        rw ←l10 hf',
        exact h,
      exact l9_exclusive_23 f'.2 hp hn},
    {apply or.intro_right,
    split,
      rw l10 hf',
      exact hn,
      by_contradiction,
      apply l9_exclusive_23 f'.2 (l11 hf' h) hn}}
 end}
end

instance : has_add 𝔼 := has_add_G 𝔼
noncomputable instance : linear_order 𝔼 := oag_is_total_ordered 𝔼 E'

--def g1 : S → 𝔼 := quotient_add_group.mk
--def f1 : S →+ 𝔼 := quotient_add_group.mk' B

def S' := quotient_add_group.left_rel B  
--lemma h1 : ∀ (x : S), x ∈ B →  f1 x = 0 := sorry 
--def adb : 𝔼 →+ 𝔼 := quotient_add_group.lift B f1 h1
--lemma h2 (h : S): adb (g1 h : 𝔼) = f1 h := quotient_add_group.lift_mk' B h1 h
def r : S → S → Prop := λ f g, (↑f : 𝔼) = ↑g  

lemma a (f g : S) : (f.1 ∘ g.1) ∈ S := 
begin 
  rcases f.2 with ⟨B, hB⟩,
  rcases g.2 with ⟨C, hC⟩,
  have h1 : ∀ x y, abs(df f.1 (g.1(x + y)- g.1 x - g.1 y) (g.1 x + g.1 y)) < B, 
    intros x y,
    exact (hB (g.1(x + y) - g.1 x - g.1 y) (g.1 x + g.1 y)),
  have h2 : ∃ D, ∀ n : ℤ, - C  + 1 ≤  n ∧ n < C → abs( f.1 n) < D,
    exact l2 f.1 C (-C + 1),
  rcases h2 with ⟨D, hD⟩,
  use (B + B + D),
  intros x y,
  specialize hB (g.1 x) (g.1 y),
  specialize hC x y,
  specialize h1 x y,
  rw df at *,
  simp only [function.comp_app] at *,
  ring_nf,
  have h3 : -C + 1 ≤ g.1 (x + y) +(-g.1 x - g.1 y) ∧ g.1 (x + y) + (-g.1 x - g.1 y) < C,
    rw abs_lt at hC,
    cases hC,
    split, 
    have hC_left': -C < g.val (x + y) +(- g.val x - g.val y),
      linarith,
      exact int.add_one_le_iff.mpr hC_left',
      linarith,
  specialize hD (g.1 (x + y) + (-g.1 x - g.1 y)) h3,
  calc abs(f.1 (g.1 (x + y)) + (-f.1 (g.1 x) - f.1 (g.1 y)))
    = abs((f.1 (g.1 (x + y)) + (-f.1 (g.1 (x + y) + (-g.1 x - g.1 y)) - f.1 (g.1 x + g.1 y)))
    + (f.1 (g.1 x + g.1 y) + (-f.1 (g.1 x) - f.1 (g.1 y))) + f.1(g.1 (x + y) + (-g.1 x - g.1 y))) : by {ring_nf,ring_nf,ring_nf}
    ...≤ abs(f.1 (g.1 (x + y)) + (-f.1 (g.1 (x + y) + (-g.1 x - g.1 y)) - f.1 (g.1 x + g.1 y))) 
    + abs(f.1 (g.1 x + g.1 y) + (-f.1 (g.1 x) - f.1 (g.1 y))) + abs(f.1 (g.1 (x + y) + (-g.1 x - g.1 y))) : abs_add_three _ _ _
    ...= abs(f.1 (g.1 (x + y)) -g.1 x - g.1 y + (-f.1 (g.1 (x + y)) - f.1 (g.1 x + g.1 y))) 
    + abs(f.1 (g.1 x + g.1 y) -f.1 (g.1 x) - f.1 (g.1 y)) + abs(f.1 (g.1 (x + y) + (-g.1 x - g.1 y))) : sorry
    ...< B + B + D : sorry
    ...= 2 * B + D : by ring
end

def S.mul : S → S → S := λ f g, ⟨λ p, (f.1 ∘ g.1) p, a f g⟩

instance : has_equiv S := ⟨r⟩

instance : setoid S := S'

lemma gjh : (@has_equiv.equiv ↥S (@setoid_has_equiv ↥S (@quotient_add_group.left_rel ↥S S.to_add_group B)) ⇒
  @has_equiv.equiv ↥S (@setoid_has_equiv ↥S (@quotient_add_group.left_rel ↥S S.to_add_group B)) ⇒
  @has_equiv.equiv ↥S (@setoid_has_equiv ↥S (@quotient_add_group.left_rel ↥S S.to_add_group B))) (S.mul) (S.mul) := 
begin
  intros f1 f2 hf g1 g2 hg,
  cases hf with B hB,
  simp only [S.mul],
  cases hg with C hC,
  have h1 : ∃ B, ∀ n : ℤ , -C ≤ n ∧ n < C + 1 → abs(f2.1 n) < B,
    exact l2 f2.1 (C + 1) (-C),
  rcases h1 with ⟨E, hE⟩,
  rcases f2.2 with ⟨D, hD⟩,
  use B + (D - 1) + (E - 1),
  intro x,
  specialize hB (g1.1 x),
  specialize hC x,
  simp only [add_subgroup.coe_add, add_subgroup.coe_neg, subtype.coe_mk, subtype.val_eq_coe] at *,
  rw l8 at *,
  specialize hD (g2.1 x - g1.1 x) (g1.1 x),
  rw df at hD,
  simp only [function.comp_app] at hD,
  ring_nf,
  rw ←subtype.val_eq_coe at *,  
  rw ←subtype.val_eq_coe at *,
  rw ←subtype.val_eq_coe at *,
  rw l7 at *,
  have h2 : -C ≤ -g1.1 x + g2.1 x ∧ -g1.1 x + g2.1 x < C + 1,
    rw abs_le at hC,
    cases hC,
    split,
      exact hC_left,
      linarith[lt_add_one C],
  specialize hE (-g1.1 x + g2.1 x) h2,
  have hE1 : abs(f2.1 (g2.1 x - g1.1 x)) ≤ E - 1,
    rw neg_add_eq_sub at hE, 
    exact int.le_sub_one_iff.mpr hE,
  rw ←int.le_sub_one_iff at hD,
  simp only [function.comp_app],
  calc abs(-f1.1 (g1.1 x) + f2.1 (g2.1 x)) = abs((-f1.1 (g1.1 x) + f2.1 (g1.1 x))
  + (f2.1 (g2.1 x) + (-f2.1 (g2.1 x - g1.1 x) - f2.1 (g1.1 x))) + f2.1 (g2.1 x - g1.1 x)) : by {ring_nf,ring_nf,}
  ... ≤ abs(-f1.1 (g1.1 x) + f2.1 (g1.1 x)) + abs(f2.1 (g2.1 x) + (-f2.1 (g2.1 x - g1.1 x) - f2.1 (g1.1 x)))
  + abs(f2.1 (g2.1 x - g1.1 x)) : abs_add_three _ _ _
  ... ≤ B + (D - 1) + (E - 1) : sorry
end

def mul :
  𝔼 → 𝔼 → 𝔼 :=
quotient.map₂' S.mul gjh

def I : ℤ → ℤ := λ x, x 
lemma I_in_S : I ∈ S := 
begin
  use 5,
  intros x y,
  rw df,
  rw I,
  tidy,
end

lemma l12 (a b c : ℤ) : a * b + a = a * (b + 1) := by {ring}

lemma l13 (m : ℕ) : abs((↑m : ℤ) + 1) = ↑m + 1 := rfl

instance : ring 𝔼 := 
begin
  refine {
  mul := mul,
  mul_assoc := 
  begin 
   intros f g h,
   tidy 
  end,
  one := quotient_add_group.mk ⟨I, I_in_S⟩,
  one_mul := 
  begin 
    intro f,
    tidy, 
  end,
  mul_one := begin intro f, tidy, end,
  left_distrib := 
  begin 
    intros f g h,
    induction h, 
    induction g, 
    induction f, 
    work_on_goal 0 {
    rcases f.2 with ⟨B, hB⟩,
    dsimp at *,
    apply quotient.eq.mpr,
    simp only [S.mul],
    use B - 1,
    intro x,
    simp,
    rw ←abs_neg,
    rw df at hB,
    simp at *,
    specialize hB (g.1 x) (h.1 x),
    rw ←int.add_one_le_iff at hB,
    have h1 : -f.1 (h.1 x) + - f.1 (g.1 x) + f.1 (g.1 x + h.1 x)
    = f.1 (g.1 x + h.1 x) -f.1 (g.1 x) -f.1 (h.1 x), ring,
    simp at *,
    rw ←h1 at hB,
    linarith}, 
    work_on_goal 1 { refl }, 
    work_on_goal 1 { refl }, 
    refl,
  end,
  right_distrib :=
  begin
    intros f g h,
    induction h, 
    induction g, 
    induction f, 
    work_on_goal 0 { refl }, 
    work_on_goal 0 { refl }, 
    work_on_goal 0 { refl }, 
    refl,
  end,
  ..𝔼.add_comm_group}
end
lemma ama (a b c: ℤ): a-b+c = a+c-b := by ring

lemma aam (a b c: ℤ): a+c-b=a-(b-c):= by ring

lemma mmm (a b c: ℤ): -c-b-a = -a+(-b-c) := by ring

lemma l14 {f : ℤ → ℤ}(hf : almost_homomorphism f) : 
∃ C, (∀ p q, abs(df f p q) < C) ∧ ∀ p q, abs(p * f q - q * f p) < (abs(p) + abs(q) + 2) * C :=  
begin
  rcases hf with ⟨C, hC⟩,
  use C,
  split,
  intros p q,
  exact hC p q,
  have h : ∀ p q, abs(f (p * q) - p * f q) < (abs p + 1) * C,
    intros p q,
    induction p with n hn,
      {induction n with m hm,
        specialize hC 0 0,
        rw df at hC,
        simp at *,
        exact hC,
        specialize hC (m * q) q,
        rw df at hC,
        simp at hC,
        simp only [int.coe_nat_succ, int.of_nat_eq_coe] at *,
        rw mul_comm at hC,
        rw l12 at hC,
        rw mul_comm at hC,
        rw (mul_comm q ↑m) at hC,
        calc abs(f ((m + 1) * q) - (m + 1) * f q) 
           = abs((f ((m + 1) * q) - f (m * q) - f q) + (f (m * q) - m * f q)) : by
        {ring_nf}
        ...≤ abs(f  ((m + 1) * q) - f (m * q) - f q) + abs(f (m * q) - m * f q) : abs_add _ _
        ...< C + (abs(m) + 1) * C : by linarith
        ...= (1 + abs(m) + 1) * C : by linarith
        ...= (abs (m + 1) + 1) * C : by {simp, rw l13, apply or.inl, ring_nf},
        exact f (f C)},
      {induction hn with m hm,
        rw ←int.neg_of_nat_of_succ at *,
        have h0 : abs(f 0) < C,
          specialize hC 0 0,
          rw df at hC,
          simp at *,
          exact hC,
        specialize hC (-q) q,
        rw df at *,
        simp at *,
        rw ←abs_neg at hC,
        simp at hC,
        rw ←sub_add at hC,
        have h1 : (1 + 1) * C = C + C, ring,
        rw h1,
        calc abs(f (- q) + f q) = abs((f q + f (- q)) -f 0 + f 0) : by {simp[add_comm]}
                             ...= abs(f q - f 0 + f (- q) + (f 0)) : by {rw ama (f q) (f 0) (f (-q))}
                             ...≤ abs(f q - f 0 + f (- q)) + abs(f 0) : abs_add _ _
                             ...< C + C : by linarith,
        rw ←int.neg_of_nat_of_succ at *,
        specialize hC ((-1 + (-m -1)) * q) q,
        rw df at hC,
        rw ←abs_neg at hC,
        simp at *,
        rw [mul_comm, l12] at hC,
        rw add_comm (-1) (-(↑m : ℤ)-1) at hC,
        simp at hC,
        rw ←neg_add' at hC,
        rw add_comm at hm,
        have h1 : (abs (-(↑m : ℤ) + -1) + 1) * C + C = (abs (-1 + (-1 + -↑m)) + 1) * C,
          ring_nf,
          rw ←abs_neg (-1 + (-1 - (↑m : ℤ))),
          simp,
          have h2 : abs((↑m : ℤ) + 1 + 1) = abs(↑(m+1)+1),
           ring_nf,
          rw h2,
          rw l13,
          rw ←abs_neg,
          simp,
          ring_nf,
          rw add_comm 1 (↑m : ℤ),
          rw l13,
          ring,
          rw ←h1,
        calc abs(f ((-1 + (-1 + -↑m)) * q) - (-1 + (-1 + -↑m)) * f q) 
           = abs((f q - (f (q * -(↑m + 1)) - f (q * (-(↑m + 1) + -1)))) + (f ((-↑m + - 1) * q) - (-↑m + -1) * f q))
           : begin 
             rw ←aam, rw mul_comm q (-((↑m : ℤ) + 1)), rw neg_add' (↑m : ℤ) 1, simp, 
           rw add_mul (-1) (-1 + (-↑m: ℤ)) (f q), ring_nf,ring_nf, 
           rw mul_comm, rw ←mmm, rw add_comm,
           end
        ...≤ abs(f q - (f (q * -(↑m + 1)) - f (q * (-(↑m + 1) + -1)))) + abs (f ((-↑m + - 1) * q) - (-↑m + -1) * f q) 
           : abs_add _ _
        ...= abs(f q - (f (q * -(↑m + 1)) - f (q * (-(↑m + 1) -1)))) + abs (f ((-↑m + - 1) * q) - (-↑m + -1) * f q) : by ring
        ...< (abs (-↑m + -1) + 1) * C + C : by linarith,
        exact f (f C)},
  intros p q,
  have h3 : abs(f (p * q) - p * f q) < (abs p + 1) * C,
     specialize h p q,
     exact h,
  specialize h q p,
  rw ←abs_neg at h3,
  simp at h3,
  rw mul_comm q p at h,
  calc abs(p * f q - q * f p) = abs((p * f q - f (p * q)) + (f (p * q) - q * f p)) : by simp only [sub_add_sub_cancel]
                          ... ≤ abs(p * f q - f (p * q)) + abs(f (p * q) - q * f p) : abs_add _ _
                          ... < (abs p + 1) * C + (abs q + 1) * C : by linarith
                          ... = (abs p + 1 + (abs q + 1)) * C : by rw ←add_mul
                          ... = (abs p + abs q + 2) * C : by ring,
end

lemma l15 {f : ℤ → ℤ}(hf : almost_homomorphism f) : ∃ A B : ℤ, ∀ p, abs(f p) < A * abs p + B :=
begin
  rcases (l14 hf) with ⟨C, hC⟩,
  cases hC with hC1 hC2,
  use (C + abs (f 1)),
  use 3 * C,
  intro p,
  specialize hC2 p 1,
  simp at hC2,
  rw ←abs_neg at hC2,
  simp at hC2,
  calc abs(f p) = abs((f p - p * f 1) + p * f 1) : by ring
             ...≤ abs(f p - p * f 1) + abs(p * f 1) : abs_add _ _
             ...< (abs p + 3) * C + abs(p * f 1) : by linarith
             ...= (abs p) * C + 3 * C + abs(p) * abs(f 1) : by rw [add_mul,abs_mul]
             ...= abs p * (C + abs(f 1)) + 3 * C : by ring
             ...= (C + abs(f 1)) * abs p + 3 * C : by rw mul_comm,
end

lemma l16 {a b c : ℤ} (hd : c > 0)(ha : a > 0)(habc : a < b): a * c < b * c := (mul_lt_mul_right hd).mpr habc

lemma l17 (a b : ℤ) (hab : a ≤ b) :  a < b + 1 := begin  exact int.lt_add_one_iff.mpr hab, end

lemma amma (a b c d: ℤ): a-b+(c-d)=a-b+c-d:= by ring

instance : comm_ring 𝔼 := 
{mul_comm := 
  begin
    intros f g,
    induction g, 
    induction f, 
    work_on_goal 0 { 
      apply quotient.eq.mpr,
      have h1 : ∃ D E, ∀ p, abs p * abs(f.1 (g.1 p) - g.1 (f.1 p)) < D * abs p + E,
        rcases (l14 f.2) with ⟨C1, hC1⟩,
        cases hC1 with _ hC1,
        rcases (l14 g.2) with ⟨C2, hC2⟩,
        cases hC2 with _ hC2,
        rcases (l15 f.2) with ⟨A1, B1, hAB1⟩,
        rcases (l15 g.2) with ⟨A2, B2, hAB2⟩,
        use (A2 * C1 + A1 * C2 + C1 + C2),
        use  (B2 * C1 + B1 * C2 + 2 * C1 + 2 * C2),
        intro p,
        specialize hC1 p (g.1 p),
        specialize hC2 (f.1 p) p,
        specialize hAB1 p,
        specialize hAB2 p,
        rw ←abs_mul,
        rw mul_sub,
        have h2 : (abs p + abs (g.1 p) + 2) > 0,
          linarith[abs_nonneg p, abs_nonneg (g.1 p)],  
        have h3 : C1 > 0,
          specialize hC1_left 11 1,
          linarith[abs_nonneg (df f.1 11 1)],
        have h4 : (abs (f.1 p) + abs p + 2) > 0,
          linarith[abs_nonneg p, abs_nonneg (f.1 p)],  
        have h5 : C2 > 0,
          specialize hC2_left 11 1,
          linarith[abs_nonneg (df g.1 11 1)],
        have h6 : (abs p + A2 * abs p + B2 + 2) > (abs p + abs (g.1 p) + 2),
          linarith, 
        have h7 : (A1 * abs p + B1 + abs p + 2) > (abs (f.1 p) + abs p + 2),
          linarith,
        calc abs (p * f.1 (g.1 p) - p * g.1 (f.1 p)) 
        = abs((p * f.1 (g.1 p) - g.1 p * f.1 p) + (f.1 p * g.1 p - p * g.1 (f.1 p)))
        : by {rw amma,rw mul_comm (f.1 p) (g.1 p),simp only [sub_add_cancel]}
     ...≤ abs(p * f.1 (g.1 p) - g.1 p * f.1 p) + abs(f.1 p * g.1 p - p * g.1 (f.1 p))
        : abs_add _ _ 
     ...< (abs p + abs (g.1 p) + 2) * C1 + (abs (f.1 p) + abs p + 2) * C2 : by linarith
     ...< (abs p + A2 * abs p + B2 + 2) * C1 + (A1 * abs p + B1 + abs p + 2) * C2 
     : by linarith[l16 h3 h2 h6, l16 h5 h4 h7]
     ...= (A2 * C1 + A1 * C2 + C1 + C2) * abs p + (B2 * C1 + B1 * C2 + 2 * C1 + 2 * C2) : by ring,
     rcases h1 with ⟨D, E, hDE⟩,
     have h2 : ∃ D, ∃ N, ∀ p, abs p > N →  abs(-f.1(g.1 p) + g.1 (f.1 p)) ≤ D,
      use max (D + 1) (abs(-f.1(g.1 0) + g.1 (f.1 0))),
      use E,
      intros p hp,
      specialize hDE p,
      simp,
      by_cases p = 0,
        apply or.intro_right,
        rw h,
        rw push_neg.not_eq at h,
        have h2 : D * abs p + E < (D + 1) * abs p,
          linarith,
        have h3 : abs p * abs(f.1 (g.1 p) - g.1 (f.1 p))  < (D + 1) * abs p,
          linarith,
        have h4 : abs p > 0 := abs_pos.mpr h,
         rw mul_comm at h3,
        rw (mul_lt_mul_right h4) at h3,
        apply or.intro_left,
        rw ←abs_neg,
        simp at *,
        rw add_comm,
        ring,
        linarith,
      rcases h2 with ⟨D1, hD1⟩,
      rcases hD1 with ⟨N, hN⟩,
      have h5 : ∃ D, ∀ p, abs p ≤ N → abs(f.1 (g.1 p) - g.1 (f.1 p)) < D,
        rcases l2 (λ x, f.1(g.1 x) - g.1(f.1 x)) (N + 1) (-N) with ⟨D, hD⟩,
        use D,
        intros p hp,
        rw abs_le at hp,
        cases hp,
        rw ←int.lt_add_one_iff at hp_right,
        specialize hD p (and.intro hp_left hp_right),
        exact hD, 
      rcases h5 with ⟨D2, hD2⟩,
      use max D1 D2,
      intro p,
      simp only [S.mul],
      simp,
      by_cases abs p > N,
        apply or.intro_left,
        exact hN p h,
        apply or.intro_right,
        simp at h,
        rw ←abs_neg,
        simp at *,
        rw add_comm,
        ring_nf,
        linarith[hD2 p h]}, 
    work_on_goal 1 { refl }, 
    refl,
  end,
  ..𝔼.ring}

  lemma l18 (f : ℤ → ℤ) : (∀ p < 0, f p = -f (-p)) → (∃ D, ∀ m n, 0 ≤ m → 0 ≤ n → abs(df f m n) < D) 
→ almost_homomorphism f :=
begin
  intros hn hp,
  rcases hp with ⟨D, hD⟩,
  use D,
  intros p q,
  by_cases hp : 0 ≤ p,
    {by_cases hq : 0 ≤ q,
      specialize hD p q hp hq,
      exact hD,
      simp at hq,
        by_cases hpq : p + q < 0,
          specialize hD p (-(p + q)) hp (neg_nonneg.mpr (le_of_lt hpq)),
          rw df at *,
          simp only [add_add_neg_cancel'_right, neg_add_rev] at *,
          have h1 : f (-q) = -f q := eq_neg_of_eq_neg (hn q hq),
          rw ←neg_add_rev at hD,
          have h2 : f(-(p + q)) = -f (p + q) := eq_neg_of_eq_neg (hn (p + q) hpq),
          rw [h1, h2] at hD,
          simp at hD,
          rw abs_lt at *,
          cases hD,
          split,
            linarith,
            linarith,
          simp at hpq,
          specialize hD (p + q) (-q) (hpq) (neg_nonneg.mpr (le_of_lt hq)),
          rw df at *,
          simp at *,
          have h1 : f (-q) = -f q := eq_neg_of_eq_neg (hn q hq),
          rw h1 at hD,
          rw ←abs_neg at hD,
          simp at hD,
          rw abs_lt at *,
          cases hD,
          split,
            linarith,
            linarith},
    { simp at hp,
      by_cases hq : 0 ≤ q,
        by_cases hpq : p + q < 0,
          specialize hD q (-(p + q)) hq (neg_nonneg.mpr (le_of_lt hpq)),
          rw df at *,
          simp at *,
          have h1 : f (-p) = -f p := eq_neg_of_eq_neg (hn p hp),
          rw ←neg_add_rev at hD,
          have h2 : f(-(p + q)) = -f (p + q) := eq_neg_of_eq_neg (hn (p + q) hpq),
          rw [h1, h2] at hD,
          simp at hD,
          rw abs_lt at *,
          cases hD,
          split,
            linarith,
            linarith,
          simp at hpq,
          specialize hD (p + q) (-p) hpq (neg_nonneg.mpr (le_of_lt hp)),
          rw df at *,
          simp at *,
          rw add_comm p q at hD,
          simp at hD,
          rw add_comm q p at hD,
          have h1 : f (-p) = -f p := eq_neg_of_eq_neg (hn p hp),
          rw h1 at hD,
          rw abs_lt at *,
          cases hD,
          split,
            linarith,
            linarith,
      simp at hq,
      specialize hD (-p) (-q) (neg_nonneg.mpr (le_of_lt hp)) (neg_nonneg.mpr (le_of_lt hq)),
      have h1 : f (-p) = -f p := eq_neg_of_eq_neg (hn p hp),
      have h2 : f (-q) = -f q := eq_neg_of_eq_neg (hn q hq),
      have h3 : p + q < 0 := by linarith,
      have h4 : f(-(p + q)) = -f (p + q) := eq_neg_of_eq_neg (hn (p + q) h3),
      rw df at *,
      simp only [] at *,
      rw [←neg_add_rev,add_comm q p, h4, h1, h2, ←abs_neg] at hD,
      simp at hD,
      rw abs_lt at *,
        cases hD,
        split,
          linarith,
          linarith}
end

lemma l19 {f : S} (hf :  ∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f.1 p > C) 
: ∀ p ≥ 0, ∃ n ≥ 0, p ≤ f.1 n ∧ ∀ m ≥ 0, m < n → f.1 m < p := 
begin
  have h1 : ∀ p > 0, ∃ (n : ℕ), p ≤ f.1 ↑n,
    intros p hp,
    specialize hf p hp,
    rcases hf with ⟨N, hN⟩,
    let N' := max 0 (N + 1),
    have hNN' : N' = max 0 (N + 1) := rfl,
    have hN': N < N',
      simp only [N'],
      linarith[le_max_right 0 (N + 1)], 
    specialize hN N' hN', 
    rcases (int.eq_coe_of_zero_le (le_max_left 0 (N + 1))) with ⟨M, hM⟩,
    use M,
    rw [hNN',hM] at hN,        
    exact le_of_lt hN,
  intros p hp,
  have h2 : ∃ (n : ℕ), p ≤ f.1 ↑n,
    by_cases hp1 : p > 0,
      exact h1 p hp1,
      simp at hp1,
      have hp2 : p = 0 := le_antisymm hp1 hp,
      rcases h1 2 _ with ⟨n, hn⟩,
      use n,
      linarith, 
      norm_num,
  rcases (nat.find_x h2) with ⟨n, hn⟩,
  simp only [] at hn, 
  use [↑n, int.coe_zero_le n],
  cases hn with hn1 hn2, 
  split,
    exact hn1,
    intros m hm hmn,
    rcases (int.eq_coe_of_zero_le hm) with ⟨m',hm'⟩,
    rw hm' at hmn,
    simp at hmn,
    specialize hn2 m' hmn,
    rw ←hm' at hn2,
    exact not_le.mp hn2,
end

def SP := {f : S | ∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f.1 p > C}
def SN := {f : S | ∀ C > 0, ∃ N : ℤ, ∀ p, p > N → f.1 p < -C}
def S0 := {f : S | ∃ B : ℤ, ∀ x : ℤ, abs (f.1 x) ≤ B}

lemma hNP0 (f : S) : f ∈ SP ∨ f ∈ S0 ∨ f ∈ SN :=  
begin
  have := l9 f.2,
  cases this,
    apply or.intro_right,
    apply or.intro_left,
    exact this,
    cases this,
      apply or.intro_left,
      exact this,
      apply or.intro_right,
      apply or.intro_right,
      exact this,
end

noncomputable def inv_fp : SP → G :=  λ f, λ p,  
if hp : 0 ≤ p then 
begin
  choose n hn using l19 f.2 p hp,
  exact n,
end
else 
begin
  choose n hn using l19 f.2 (-p) (le_of_lt (neg_pos.mpr (not_le.mp hp))),
  exact -n,
end

lemma inv_fp.neg {f : SP}{p : ℤ}(hp : p < 0) : (inv_fp f) p = - (inv_fp f (-p)) := 
begin
  simp only [inv_fp],
  split_ifs with hp1 hp2,
    exfalso,
      linarith,
    simp,
    exfalso,
      linarith,
end

@[simp] lemma l20 {f : S} :  (-f).1 = -f.1 := rfl

lemma neg_posS {f : S} : f ∈ SN → -f ∈ SP := 
begin
  intros hf C hC,
  rcases hf C hC with ⟨N, hN⟩,
  use N,
  intros p hp,
  specialize hN p hp,
  rw [l20, l7],
  linarith, 
end

noncomputable def inv_fn : SN → G := λ f, -inv_fp ⟨-f, neg_posS (subtype.coe_prop f)⟩

lemma bdd_fx_fnx (f : SP) : ∃ B, ∀ x, abs (f.1.1 x + f.1.1 (-x)) < B := 
begin
  rcases f.1.2 with ⟨B,hB⟩,
      use B + abs (f.1.1 0),
      intro y,
      specialize hB y (-y),
      simp only [df] at hB,
      rw ←abs_neg at hB,
      ring_nf at hB,
      ring_nf at hB,
      ring_nf at hB,
      rw neg_add_eq_sub at hB,
      calc abs(f.1.1 y + f.1.1 (-y)) = abs((f.1.1 y + f.1.1 (-y) - f.1.1 0) + f.1.1 0) : by simp only [sub_add_cancel]
                                  ...≤ abs(f.1.1 y + f.1.1 (-y) - f.1.1 0) + abs(f.1.1 0) : abs_add _ _ 
                                  ...< B + abs(f.1.1 0) : by linarith,
end

lemma not_all_bdd_range (f : SP) {A : set ℤ}
(h1 : ∃ B, ∀ x ∈ A, abs (f.1.1 x) < B) : ¬∀ C, ∃ x ∈ A, abs x ≥ C :=
begin
  by_contradiction h2,
  rcases h1 with ⟨B1,hB1⟩,
  rcases bdd_fx_fnx f with ⟨B2,hB2⟩,
  have hB20 : B2 > 0,
    specialize hB2 0,
    linarith[abs_nonneg (f.1.1 0 + f.1.1 (-0))],
  have hB0 : max B1 B2 + max B1 0 > 0 := by linarith[le_max_right B1 B2, le_max_right B1 0],
  have:= f.2 (max B1 B2 + max B1 0)  hB0,
  rcases this with ⟨N,hN⟩,
  specialize h2 (N + 1),
  rcases h2 with ⟨x, hxA, hx⟩,
  specialize hB1 x hxA,
  by_cases hx0 : x ≥ 0,
    rw (abs_of_nonneg hx0) at hx,
  have hxn : x > N := by linarith,
    specialize hN x hx,
    rw abs_lt at hB1,
    cases hB1,
    linarith[le_max_left B1 B2, le_max_right B1 0],  
    rw (abs_of_neg (not_le.mp hx0)) at hx,
    specialize hB2 x,
    have habsfnx : abs(f.1.1 (-x)) < max B1 B2 + max B1 0,
      rw ←abs_neg (f.1.1 x) at hB1,
      rw add_comm at hB2,
      calc abs(f.1.1 (-x)) = abs((f.1.1 (-x) + f.1.1 x) + (-f.1.1 (x))) : by {ring_nf,simp only [add_sub_cancel]}
                       ... ≤ abs(f.1.1 (-x) + f.1.1 x) + abs(-f.1.1 x) : abs_add _ _
                       ... < max B1 B2 + abs(-f.1.1 x) : by linarith[le_max_right B1 B2]
                       ... < max B1 B2 + max B1 0 : by linarith[le_max_left B1 0],
    specialize hN (-x) hx,
    rw abs_lt at habsfnx,
    cases habsfnx,
    linarith,
end

lemma bdd_range (f : SP) {A : set ℤ}
(h1 : ∃ B, ∀ x ∈ A, abs (f.1.1 x) < B) : ∃ C, ∀ x ∈ A, abs x < C :=
begin
  have := not_all_bdd_range f h1,
  simp at this,
  exact this,
end
 
lemma inv_fp_0 (f : SP) (m : ℤ) (hm : 0 ≤ m ∧ m ≤ f.1.1 0) : inv_fp f m = 0 := 
begin
  simp only [inv_fp],
  split_ifs,
    have h1 := classical.some_spec (l19 f.2 m h),
    rcases h1 with ⟨h1,h2,h3⟩,
    apply le_antisymm,
    specialize h3 0 _,
    norm_num,
    have h0 := mt h3,
    simp only [not_lt] at h0,
    cases hm with h hm,
    exact h0 hm,
    exact h1,
    cases hm with h1 h2,
    exfalso,
    exact h h1,
end 

lemma increasing_inv_fp (f : SP) {m n : ℤ} (hn : 0 ≤ n)(hmn : n < m) : inv_fp f m ≥ inv_fp f n :=
begin
  simp only [inv_fp],
  split_ifs,
  have h1 := classical.some_spec (l19 f.2 m h),
  have h2 := classical.some_spec (l19 f.2 n hn),
  rcases h1 with ⟨h11,h12,h13⟩,
  rcases h2 with ⟨h21,h22,h23⟩,
  set gm := classical.some (l19 f.2 m h) with hgm,
  set gn := classical.some (l19 f.2 n hn) with hgn,
  rw ←hgm at *,
  rw ←hgn at *,
  specialize h23 gm h11,
  have h3 : f.1.1 gm ≥ n := by linarith,
  exact not_lt.mp ((not_imp_not.mpr h23) (not_lt.mpr h3)),
  exfalso,
  simp at h,
  linarith, 
end

lemma inv_fp_pos (f : SP) {m : ℤ} (hm1 : 0 ≤ m ∧ f.1.1 0 < m) : inv_fp f m > 0 := 
begin
  simp only [inv_fp],
    split_ifs,
    have h1 := classical.some_spec (l19 f.2 m h),
    by_contradiction hn,
    rcases h1 with ⟨h2,h3,h4⟩,
    have := le_antisymm h2 (not_lt.mp hn),
    rw ←this at h3,
    cases hm1,
    linarith,
    exfalso,
    linarith[not_le.mp h], 
end

lemma bound_m {f : SP} : ∀ m ∈ {m : ℤ | 0 ≤ m ∧ f.1.1 0 < m}, f.1.1 (inv_fp f m) ≥ m 
∧ m > f.1.1 (inv_fp f m - 1) := 
begin
  intros m hm,
  have h0 := inv_fp_pos f hm, 
  have h1 : inv_fp f m > 0 := inv_fp_pos f hm,
  simp only [inv_fp] at *,
  split_ifs at h0,
  split_ifs,
    have h2 := classical.some_spec (l19 f.2 m (and.left hm)),
    set n := classical.some (l19 f.2 m (and.left hm)),
    rcases h2 with ⟨h21,h22,h23⟩,
    split,
      exact h22,
      have hn : n - 1 ≥ 0 := by linarith[int.add_one_le_iff.mpr h0],
      specialize h23 (n - 1) hn (sub_one_lt n),
      exact h23,
    cases hm,
    linarith,
end

lemma lemma_f (f : SP) : ∀ m n l ∈ {m : ℤ | 0 ≤ m ∧ f.1.1 0 < m}, 
f.1.1 (inv_fp f l - 1) - f.1.1 (inv_fp f m) - f.1.1 (inv_fp f n) < l - m - n ∧ 
l - m - n < f.1.1 (inv_fp f l) - f.1.1 (inv_fp f m -1) - f.1.1 (inv_fp f n - 1) := 
begin
  intros m n l hm hn hl,
  have h1 := bound_m m hm,
  have h2 := bound_m n hn,
  have h3 := bound_m l hl,
  cases h1, cases h2, cases h3,
  split,
    linarith,
    linarith,
end

@[simp] lemma tri (a b c : ℤ) : a - b - c + (b + c) = a := by ring

lemma lemma_f1 (f : S) : ∃ C, ∀ m, abs(-f.1 m + f.1(m - 1)) < C := 
begin
  rcases f.2 with ⟨C, hC⟩,
  use C + abs(f.1 1),
  intro m,
  specialize hC (m - 1) 1,
  rw ←abs_neg at hC,
  simp [df] at hC,
  rw ←subtype.val_eq_coe at hC,
  ring_nf at hC,
  rw add_comm at hC,
  calc abs (-f.1 m + f.1 (m - 1)) = abs((-f.1 m + f.1 (m - 1) + f.1 1) + (-f.1 1)) : by {ring_nf,simp only [add_sub_cancel]}
                               ...≤ abs(-f.1 m + f.1 (m - 1) + f.1 1) + abs(-f.1 1) : abs_add _ _ 
                               ...< C + abs(-f.1 1) : by linarith
                               ...= C + abs(f.1 1) : by rw abs_neg _, 
end

lemma pref2 (a b c d e f g: ℤ): a-b+c+(-d+e)+(-f+g)=a-b+c-d+e-f+g := by ring

lemma lemma_f2 (f : S) : ∃ C, ∀ m n l, 
abs(f.1 (l - m - n) - (f.1 l - f.1 (m - 1) - f.1(n - 1))) < C :=    
begin
  rcases f.2 with ⟨C, hC⟩,
  rcases lemma_f1 f with ⟨D, hD⟩,
  use 2 * C + 2 * D,
  intros m n l,
  have h1 : abs(f.1(l - m - n) - f.1 l + f.1 (m + n)) < C,
    specialize hC (l - m -n) (m + n),
    simp only [df] at hC,
    rw ←abs_neg at hC,
    simp only [neg_sub] at hC,
    ring_nf at hC,
    rw add_comm at hC,
    rw neg_add_eq_sub at hC,
    rw tri at hC,
    exact hC,
  have h2 : abs(-f.1 (m + n) + f.1 m + f.1 n) < C,
    specialize hC m n,
    simp only [df] at hC,
    rw ←abs_neg at hC,
    ring_nf at hC,
    ring_nf at hC,
    rw ←add_assoc at hC,
    exact hC,
  have h3 : abs(-f.1 n + f.1 (n - 1)) < D,
    exact hD n,
  have h4 : abs(-f.1 m + f.1 (m - 1)) < D,
    exact hD m,  
  have h5 : -f.1 n -f.1 m + f.1 (m - 1) + f.1 (n - 1)= (-f.1 n + f.1 (n - 1)) + (-f.1 m + f.1 (m - 1)),
    ring,
  calc abs(f.1 (l - m - n) - (f.1 l - f.1 (m - 1) - f.1(n - 1))) 
  = abs((f.1(l - m - n) - f.1 l + f.1 (m + n)) + (-f.1 (m + n) + f.1 m + f.1 n) + (-f.1 n -f.1 m 
  + f.1 (m - 1) + f.1 (n - 1))) : by {ring_nf,ring_nf,ring_nf}
  ...≤ abs(f.1(l - m - n) - f.1 l + f.1 (m + n)) + abs(-f.1 (m + n) + f.1 m + f.1 n) + abs(-f.1 n -f.1 m 
  + f.1 (m - 1) + f.1 (n - 1)) : abs_add_three _ _ _
  ...= abs(f.1(l - m - n) - f.1 l + f.1 (m + n)) + abs(-f.1 (m + n) + f.1 m + f.1 n) 
  + abs((-f.1 n + f.1 (n - 1)) + (-f.1 m + f.1 (m - 1))) : by rw h5
  ...≤ abs(f.1(l - m - n) - f.1 l + f.1 (m + n)) + abs(-f.1 (m + n) + f.1 m + f.1 n)
  + abs(-f.1 n + f.1 (n - 1)) + abs(-f.1 m + f.1 (m - 1)) 
  : by linarith[abs_add (-f.1 n + f.1 (n - 1)) (-f.1 m + f.1 (m - 1))]
  ...< C + C + D + D : by linarith
  ...= 2 * C + 2 * D : by ring,
end

lemma lemma_f3 (f : S) : ∃ C, ∀ m n l, 
abs(f.1 (l - m - n) - (f.1 (l - 1) - f.1 m - f.1 n)) < C := 
begin
  rcases f.2 with ⟨C,hC⟩,
  rcases lemma_f1 f with ⟨D, hD⟩,
  use 2 * C + D,
  intros m n l,
  have h1 : abs(f.1(l - m - n) - f.1 l + f.1 (m + n)) < C,
    specialize hC (l - m -n) (m + n),
    simp only [df] at hC,
    rw ←abs_neg at hC,
    simp only [neg_sub] at hC,
    ring_nf at hC,
    rw add_comm at hC,
    rw neg_add_eq_sub at hC,
    rw tri at hC,
    exact hC,
  rw ←neg_add_eq_sub at h1,
  have h2 : abs(-f.1 (m + n) + f.1 m + f.1 n) < C,
    specialize hC m n,
    simp only [df] at hC,
    rw ←abs_neg at hC,
    ring_nf at hC,
    ring_nf at hC,
    rw ←add_assoc at hC,
    exact hC,
  have h3 : abs(-f.1 (l -1) + f.1 l) < D,
    specialize hD l,
    rw ←abs_neg at hD,
    simp only [neg_add_rev, neg_neg] at hD,
    exact hD,
  calc abs(f.1 (l - m - n) - (f.1 (l - 1) - f.1 m - f.1 n)) 
     = abs((-f.1 (l -1) + f.1 l) + (-f.1 l + f.1 (l - m - n) + f.1(m + n)) +
       (-f.1(m + n) + f.1 m + f.1 n)) : 
  begin ring_nf,ring_nf,rw ←add_assoc, rw add_comm (f.1 (l + (-m - n)))(-f.1(l -1)), ring_nf, rw add_assoc,ring_nf, end
  ...≤ abs(-f.1 (l -1) + f.1 l) + abs(-f.1 l + f.1 (l - m - n) + f.1(m + n)) 
       + abs(-f.1(m + n) + f.1 m + f.1 n) : abs_add_three _ _ _
  ...< D + C + C : by linarith
  ...= D + 2 * C : by ring
  ...= 2 * C + D : add_comm _ _, 
end 

lemma lemma_f4 (f : SP)(hf : f.1.1 0 ≥ 0) : ∀ m ∈ {m : ℤ | 0 ≤ m ∧ f.1.1 0 < m}, 
∀ n ∈ {m : ℤ | 0 ≤ m ∧ m ≤ f.1.1 0},  f.1.1 (inv_fp f (m + n) - 1) - f.1.1 (inv_fp f m) < n ∧ 
n < f.1.1 (inv_fp f (m + n)) - f.1.1 (inv_fp f m -1) := 
begin
  intros m hm n hn,
  have hmn : m + n ∈ {m : ℤ | 0 ≤ m ∧ f.1.1 0 < m},
    cases hm, 
    cases hn,
    split,
      linarith,
      linarith, 
  have h1 := bound_m m hm,
  have h2 := bound_m (m + n) hmn,
  cases h1, cases h2,
  split,
    linarith,
    linarith,
end

lemma lemma_f5 (f : S) : ∃ C, ∀ m l, abs(f.1 (l - m) - (f.1 (l - 1) - f.1 m)) < C :=
begin
  rcases f.2 with ⟨C1, hC1⟩,
  rcases lemma_f1 f with ⟨C2, hC2⟩,
  use C1 + C2,
  intros m l,
  specialize hC1 (l - m) m,
  rw ←abs_neg at hC1,
  simp only [df] at hC1,
  ring_nf at hC1,
  ring_nf at hC1,
  specialize hC2 l,
  rw ←abs_neg at hC2,
  simp only [neg_add_rev, neg_neg] at hC2,
  rw ←add_assoc at hC1,
  calc  abs(f.1(l - m) - (f.1 (l - 1) - f.1 m)) 
      = abs((-f.1(l - 1) + f.1 l) + (-f.1 l + f.1 (l - m) + f.1 m)) : 
    by {ring, ring, rw ←add_assoc, rw add_comm (f.1 (l - m)) (-f.1 (l - 1)), rw add_assoc}
  ... ≤ abs(-f.1(l - 1) + f.1 l) + abs(-f.1 l + f.1 (l - m) + f.1 m) : abs_add _ _
  ... < C1 + C2 : by linarith,
end

lemma lemma_f6 (f : S) : ∃ C, ∀ m l, abs(f.1 (l - m) - (f.1 l - f.1 (m - 1))) < C :=
begin
  rcases f.2 with ⟨C1, hC1⟩,
  rcases lemma_f1 f with ⟨C2, hC2⟩,
  use C1 + C2,
  intros m l,
  specialize hC1 (l - m) m,
  rw ←abs_neg at hC1,
  simp only [df] at hC1,
  ring_nf at hC1,
  ring_nf at hC1,
  specialize hC2 m,
  calc abs(f.1 (l - m) - (f.1 l - f.1 (m - 1))) 
     = abs((-f.1 l + (f.1 (l - m) + f.1 m)) + (-f.1 m + f.1 (m - 1))) : 
     by {ring_nf,rw ←add_assoc, rw add_comm (f.1 (l - m)) (-f.1 l),ring_nf,ring_nf}
  ...≤ abs(-f.1 l + (f.1 (l - m) + f.1 m)) + abs(-f.1 m + f.1 (m - 1)) : abs_add _ _ 
  ...< C1 + C2 : by linarith, 
end

lemma abs_pos_lt {a b : ℤ}(ha : a ≥ 0)(hab : b > a) : abs b > abs a := 
begin
  have hb : b > 0 := by linarith,
  rw [abs_of_pos hb,abs_of_nonneg ha],
  exact hab,
end

lemma abs_neg_lt {a b : ℤ}(ha : a < 0)(hab : a > b) : abs b > abs a := 
begin
  have hb : b < 0 := by linarith,
  rw [abs_of_neg hb, abs_of_neg ha],
  exact neg_lt_neg hab,
end

lemma l21_1 (f : SP) : ∃ (D : ℤ), ∀ (m n : ℤ), f.1.1 0 < m ∧ 0 ≤ m
→ f.1.1 0 < n ∧ 0 ≤ n → abs (df (inv_fp f) m n) < D := 
begin
  let A := {m : ℤ | 0 ≤ m ∧ f.1.1 0 < m},
  have h1 : ¬∀ D, ∃ m n ∈ A, abs(f.1.1 (inv_fp f (m + n) - inv_fp f m - inv_fp f n)) ≥ D,
    have h2 : ∃ D, ∀ m n ∈ A, abs(f.1.1 (inv_fp f (m + n) - inv_fp f m - inv_fp f n) -
    (f.1.1(inv_fp f (m + n)) - f.1.1 (inv_fp f m - 1) - f.1.1 (inv_fp f n - 1))) < D,
      rcases lemma_f2 f with ⟨D,hD⟩,   
      use D,
      intros m n hm hn,
      exact hD (inv_fp f m) (inv_fp f n) (inv_fp f (m + n)),
    have h3 : ∃ D, ∀ m n ∈ A, abs(f.1.1 (inv_fp f (m + n) - inv_fp f m - inv_fp f n) -
    (f.1.1(inv_fp f (m + n) - 1) - f.1.1 (inv_fp f m) - f.1.1 (inv_fp f n))) < D,
      rcases lemma_f3 f with ⟨D,hD⟩,   
      use D,
      intros m n hm hn,
      exact hD (inv_fp f m) (inv_fp f n) (inv_fp f (m + n)),
    by_contradiction,
      rcases h2 with ⟨D1,hD1⟩,
      rcases h3 with ⟨D2,hD2⟩,
      specialize h (max D1 D2), 
      rcases h with ⟨m,n,hm,hn,hmn⟩,
      specialize hD1 m n hm hn,
      specialize hD2 m n hm hn,
      have hmn : m + n ∈ A := by {cases hm,cases hn, split, linarith, linarith},
    have h4 : f.1.1(inv_fp f (m + n) - 1) - f.1.1 (inv_fp f m) - f.1.1 (inv_fp f n) < 0,
      linarith[and.left (lemma_f f m n (m + n) hm hn hmn)],
    have h5 : f.1.1(inv_fp f (m + n)) - f.1.1 (inv_fp f m - 1) - f.1.1 (inv_fp f n - 1) > 0,
      linarith[and.right (lemma_f f m n (m + n) hm hn hmn)],
    by_cases ha : f.1.1 (inv_fp f (m + n) - inv_fp f m - inv_fp f n) ≥ 0,
      have h6 : f.1.1 (inv_fp f (m + n) - inv_fp f m - inv_fp f n) -
    (f.1.1(inv_fp f (m + n) - 1) - f.1.1 (inv_fp f m) - f.1.1 (inv_fp f n))
      > f.1.1 (inv_fp f (m + n) - inv_fp f m - inv_fp f n) := by linarith,
      linarith[le_max_right D1 D2,abs_pos_lt ha h6],
      have h8 : f.1.1 (inv_fp f (m + n) - inv_fp f m - inv_fp f n) -
    (f.1.1(inv_fp f (m + n)) - f.1.1 (inv_fp f m - 1) - f.1.1 (inv_fp f n - 1)) < 
    f.1.1 (inv_fp f (m + n) - inv_fp f m - inv_fp f n):= by linarith,
      rw not_le at ha,
      linarith[le_max_left D1 D2,abs_neg_lt ha h8],
      simp only [not_exists,not_forall,not_le] at h1,
      have hB : ∃ D, ∀ x ∈ {x : ℤ | ∃ m n ∈ A, x = inv_fp f (m + n) - inv_fp f m - inv_fp f n},
      abs(f.1.1 x) < D, 
        rcases h1 with ⟨D, hD⟩,
        use D,
        intros x hx,
        rcases hx with ⟨m, n,hm,hn,hmn⟩,
        specialize hD m n hm hn,
        rw hmn,
        exact hD,
      rcases bdd_range f hB with ⟨D,hD⟩,
      use D,
      intros m n hm hn,
      let x := inv_fp f (m + n) - inv_fp f m - inv_fp f n,
      have : x = inv_fp f (m + n) - inv_fp f m - inv_fp f n := rfl,
      have hx : x ∈ {x : ℤ | ∃ m n ∈ A, x = inv_fp f (m + n) - inv_fp f m - inv_fp f n},
        use [m, n, hm.right,hm.left,hn.right,hn.left],
      specialize hD x hx,
      rw this at hD,
      simp only [df],
      exact hD,
end

lemma l21_2 (f : SP) (hf0 : f.1.1 0 ≥ 0) : ∃ (D : ℤ), ∀ (m n : ℤ), f.1.1 0 < m → 0 ≤ n ∧ n ≤ f.1.1 0 
→ abs (df (inv_fp f) m n) < D := 
begin
  let A := {m : ℤ | 0 ≤ m ∧ f.1.1 0 < m},
  let B := {m : ℤ | 0 ≤ m ∧ m ≤ f.1.1 0},
  have h1 : ¬∀ D, ∃ (m ∈ A)(n ∈ B), abs(f.1.1 (inv_fp f (m + n) - inv_fp f m)) ≥ D,
    have h2 : ∃ D, ∀ (m ∈ A)(n ∈ B), abs(f.1.1 (inv_fp f (m + n) - inv_fp f m) - 
    (f.1.1 (inv_fp f (m + n) - 1) - f.1.1 (inv_fp f m))) < D,
      rcases lemma_f5 f with ⟨D,hD⟩,
      use D,
      intros m hm n hn,
      exact hD (inv_fp f m) (inv_fp f (m + n)),
    have h3 : ∃ D, ∀ (m ∈ A)(n ∈ B), abs(f.1.1 (inv_fp f (m + n) - inv_fp f m) - 
    (f.1.1 (inv_fp f (m + n)) - f.1.1 (inv_fp f m - 1))) < D,
      rcases lemma_f6 f with ⟨D,hD⟩,
      use D,
      intros m hm n hn,
      exact hD (inv_fp f m) (inv_fp f (m + n)),
    by_contradiction,
      rcases h2 with ⟨D1,hD1⟩,
      rcases h3 with ⟨D2,hD2⟩,
      specialize h (max D1 D2 + f.1.1 0), 
      rcases h with ⟨m,hm,n,hn,hmn⟩,
      specialize hD1 m hm n hn,
      specialize hD2 m hm n hn,
      have hmnA : m + n ∈ A := by {cases hm,cases hn, split, linarith, linarith},
      have h4 : f.1.1 (inv_fp f (m + n) - 1) - f.1.1 (inv_fp f m) < n,
        exact and.left (lemma_f4 f hf0 m hm n hn),
      have h5 : n < f.1.1 (inv_fp f (m + n)) - f.1.1 (inv_fp f m -1),
        exact and.right (lemma_f4 f hf0 m hm n hn),
      by_cases ha : f.1.1 (inv_fp f (m + n) - inv_fp f m) - f.1.1 0 ≥ 0,
        have h6 : f.1.1 (inv_fp f (m + n) - inv_fp f m) - (f.1.1 (inv_fp f (m + n) - 1)
      - f.1.1 (inv_fp f m)) > f.1.1(inv_fp f (m + n) - inv_fp f m) - f.1.1 0,
          linarith[and.right hn],
        have h7 : abs(f.1.1(inv_fp f (m + n) - inv_fp f m) - f.1.1 0) < D1,
          linarith[abs_pos_lt ha h6],
        rw [abs_of_nonneg ha, sub_lt_iff_lt_add] at h7,
        have h8 : f.1.1(inv_fp f (m + n) - inv_fp f m) ≥ 0 := by linarith,
        rw abs_of_nonneg h8 at hmn,
        linarith[le_max_left D1 D2],
        by_cases hb : f.1.1(inv_fp f (m + n) - inv_fp f m) < 0,
          have h9 : f.1.1 (inv_fp f (m + n) - inv_fp f m) - (f.1.1 (inv_fp f (m + n))
          - f.1.1 (inv_fp f m - 1)) < f.1.1(inv_fp f (m + n) - inv_fp f m), 
            linarith[and.left hn],
          have h10 : D2 > abs(f.1.1(inv_fp f (m + n) - inv_fp f m)),
            linarith[abs_neg_lt hb h9],
          linarith[le_max_right D1 D2],
          rw abs_of_nonneg (not_lt.mp hb) at hmn,
          linarith[not_le.mp ha,abs_nonneg (f.1.1 (inv_fp f (m + n) - inv_fp f m) - 
          (f.1.1 (inv_fp f (m + n)) - f.1.1 (inv_fp f m - 1))), le_max_right D1 D2],
  simp only [not_exists,not_forall,not_le] at h1,        
  have hB : ∃ D, ∀ x ∈ {x : ℤ | ∃ (m ∈ A)(n ∈ B), x = inv_fp f (m + n) - inv_fp f m},
    abs(f.1.1 x) < D, 
    rcases h1 with ⟨D, hD⟩,
    use D,
    intros x hx,
    rcases hx with ⟨m,hm,n,hn,hmn⟩,
    specialize hD m hm n hn,
    rw hmn,
    exact hD, 
  rcases bdd_range f hB with ⟨D,hD⟩,
  use D,
  intros m n hm hn,
  let x := inv_fp f (m + n) - inv_fp f m,
  have : x = inv_fp f (m + n) - inv_fp f m:= rfl,
  have hx : x ∈ {x : ℤ | ∃ (m ∈ A)(n ∈ B), x = inv_fp f (m + n) - inv_fp f m},
    have hm0 : m > 0 := by linarith,
    use [m,le_of_lt hm0,hm,n,hn],
    specialize hD x hx,
    rw this at hD,
    simp only [df],
    rw inv_fp_0 f n hn,
    simp,
    exact hD, 
end

lemma l21_3 (f : SP) (hf0 : f.1.1 0 ≥ 0): ∃ (D : ℤ), ∀ (m n : ℤ), 
0 ≤ m ∧ m ≤ f.1.1 0 → 0 ≤ n ∧ n ≤ f.1.1 0 → abs (df (inv_fp f) m n) < D := 
begin
  let C : set ℤ := {m : ℤ | 0 ≤ m ∧ m ≤ f.1.1 0},
  have hC : finite C :=
    ⟨fintype.of_finset (finset.Ico 0 (f.1.1 0 + 1)) (by simp [int.lt_add_one_iff])⟩,
  have h1 : bdd_above (image2 (df (inv_fp f)) C C) := 
    finite.bdd_above (finite.image2 (df (inv_fp f)) hC hC),
  have h2 : bdd_below (image2 (df (inv_fp f)) C C) := 
    finite.bdd_below (finite.image2 (df (inv_fp f)) hC hC),
  rcases h1 with ⟨B1,hB1⟩,
  rcases h2 with ⟨B2,hB2⟩,
  rw mem_upper_bounds at hB1,
  rw mem_lower_bounds at hB2,
  use (max (abs(B1)) (abs(B2))) + 1,
  intros m n hm hn,
  have hmC : m ∈ C := hm,
  have hnC : n ∈ C := hn,
  specialize hB1 (df (inv_fp f) m n) (mem_image2_of_mem hmC hnC),
  specialize hB2 (df (inv_fp f) m n) (mem_image2_of_mem hmC hnC),
  rw abs_lt,
  split,
   {have h5 : B2 > -(max (abs(B1)) (abs(B2))+ 1),
    calc B2 >= -abs(-B2) : neg_le.mp (le_abs_self (-B2))
        ... =  -abs(B2) : by simp
        ... >= -(max  (abs(B1)) (abs(B2))) : neg_le_neg_iff.mpr (le_max_right _ _)
        ... > -(max  (abs(B1)) (abs(B2)) + 1) : by linarith,
     linarith},
   {have h4 : B1 <  max (abs(B1)) (abs(B2)) + 1,
    calc B1 ≤ abs(B1) : le_abs_self _
       ... ≤ max  (abs(B1)) (abs(B2)) : le_max_left (abs(B1)) (abs(B2))
       ... < max (abs(B1)) (abs(B2)) + 1 : by linarith,
    linarith}
end

lemma l21 (f : SP) : ∃ (D : ℤ), ∀ (m n : ℤ), 0 ≤ m → 0 ≤ n → abs (df (inv_fp f) m n) < D := 
begin
  rcases l21_1 f with ⟨D1,hD1⟩,
  by_cases h1 : f.1.1 0 ≥ 0,
    rcases l21_2 f h1 with ⟨D2,hD2⟩,
    rcases l21_3 f h1 with ⟨D3,hD3⟩,
    let D4 := max D2 D3,
    have hD24 : D4 ≥ D2 := le_max_left D2 D3,
    have hD34 : D4 ≥ D3 := le_max_right D2 D3,
    use (max D1 D4),
    intros m n hm hn,
      by_cases hmf : m > f.1.1 0,
        by_cases hnf : n > f.1.1 0,
          specialize hD1 m n (and.intro hmf hm) (and.intro hnf hn),
          linarith[le_max_left D1 D4],
          specialize hD2 m n hmf (and.intro hn (not_lt.mp hnf)),
          linarith[le_max_right D1 D4],
        by_cases hnf : n > f.1.1 0,
          specialize hD2 n m hnf (and.intro hm (not_lt.mp hmf)),
          simp only [df] at *,
          rw [add_comm, sub_right_comm],
          linarith[le_max_right D1 D4],
          specialize hD3 m n (and.intro hm (not_lt.mp hmf)) (and.intro hn (not_lt.mp hnf)),
          linarith[le_max_right D1 D4],
    use D1,
    intros m n hm hn,
    have hmf : m > f.1.1 0 := by linarith, 
    have hnf : n > f.1.1 0 := by linarith,
    specialize hD1 m n (and.intro hmf hm) (and.intro hnf hn),
    linarith, 
end

lemma l22 (f : SP) : (inv_fp f) ∈ S := 
begin
  apply l18,
  intros p hp,
  exact inv_fp.neg hp,
  exact l21 f,
end

lemma inv_mul_one_pos.pos (f : SP) : ∃ C, ∀ m ∈ {m : ℤ | 0 ≤ m ∧ f.1.1 0 < m}, 
abs (f.1.1 (inv_fp f m) - I m) < C :=
begin
  rcases lemma_f1 f.1 with ⟨C,hC⟩,
  have hC0 : C > 0 := by linarith[abs_nonneg (-f.1.1 0 + f.1.1(0 - 1)),hC 0],
  use C,
  intros m hm,
  have := bound_m m hm,
  cases this with h1 h2,
  have hf0 : f.1.1 (inv_fp f m) - I m ≥ 0, simp only [I], linarith,
  rw abs_of_nonneg hf0,
  have h1 : f.1.1 (inv_fp f m - 1) > f.1.1 (inv_fp f m) - C,
    specialize hC (inv_fp f m),
    rw abs_lt at hC,
    cases hC,
    linarith,
  have h2 : m > f.1.1 (inv_fp f m) - C := by linarith,
  simp only [I],
  linarith,
end

lemma inv_mul_one.pos (f : SP) : ∃ C, ∀ m ≥ 0, abs (f.1.1 (inv_fp f m) - I m) ≤ C := 
begin
  rcases inv_mul_one_pos.pos f with ⟨C,hC⟩,
  use max C (abs(f.1.1 0)) + 1, 
  intros m hm,
  by_cases hf0 : 0 ≤ f.1.1 0,
    by_cases hmf : m ≤ f.1.1 0,
    rw (inv_fp_0 f m (and.intro hm hmf)),
    have h1 : f.1.1 0 - I m ≥ 0, simp only [I], linarith,
    have h2 : abs(f.1.1 0 - I m) ≤ abs(f.1.1 0), 
      rw abs_of_nonneg hf0, rw abs_of_nonneg h1, simp only [I], linarith,
    linarith[le_max_right C (abs(f.1.1 0))],
    linarith[le_max_left C (abs(f.1.1 0)), hC m (and.intro hm (not_le.mp hmf))],
  have hmf : m > f.1.1 0 := by linarith[not_le.mp hf0],
  linarith[le_max_left C (abs(f.1.1 0)), hC m (and.intro hm hmf)],
end

lemma inv_mul_one (f : SP) : ∃ C, ∀ m, abs (f.1.1 (inv_fp f m) - I m) < C := 
begin
  rcases inv_mul_one.pos f with ⟨C,hC⟩,
  rcases f.1.2 with ⟨C2,hC2⟩,
  have hC20 : C2 > 0 := by linarith[abs_nonneg (df f.1.1 0 0),hC2 0 0], 
  use C + C2 + abs(f.1.1 0),
  intro m,
  by_cases hm : m ≥ 0, 
    linarith[hC m hm,abs_nonneg (f.1.1 0)],
    simp at hm,
    rw inv_fp.neg hm,
    have hI : ∀ y : ℤ, -I (-y) = I y := λ y, by simp [I],
    rw [←hI,sub_neg_eq_add],
    specialize hC (-m) (le_of_lt (neg_pos.mpr hm)),
    rw [←abs_neg,neg_sub] at hC,
    specialize hC2 (inv_fp f (-m)) (- inv_fp f (-m)),
    rw ←abs_neg at hC2, 
    simp only [df, add_right_neg, add_right_neg] at hC2,
    ring_nf at hC2,
    rw add_comm at hC2,
    ring_nf at hC2,
    calc abs(f.1.1 (-inv_fp f (-m)) + I (-m)) = abs((I (-m) - f.1.1 (inv_fp f (-m))) + 
    (f.1.1 (inv_fp f (-m)) + f.1.1 (- inv_fp f (-m)) - f.1.1 0) + f.1.1 0) : by {ring_nf,ring_nf,ring_nf,rw add_comm}
    ...≤ abs(I (-m) - f.1.1 (inv_fp f (-m))) + abs(f.1.1 (inv_fp f (-m)) + 
         f.1.1 (- inv_fp f (-m)) - f.1.1 0) + abs(f.1.1 0) : abs_add_three _ _ _
    ...< C + C2 + abs(f.1.1 0) : by linarith,         
end

lemma tri2 (a b : ℤ) : -(a - b) = -a + b := by ring

lemma tri3 (a b c: ℤ) : a + (-b +c) = a+(c-b) := by ring 

lemma inv_mul_one.neg (f : S)(hf : f ∈ SN) : 
∃ C, ∀ m, abs (f.1 (-inv_fp ⟨-f,neg_posS hf⟩ m) - I m) ≤ C :=
begin
  rcases f.2 with ⟨C1,hC1⟩,
  rcases inv_mul_one ⟨-f,neg_posS hf⟩ with ⟨C2,hC2⟩,
  use abs(f.1 0) + C1 + C2,
  simp only [l7, l20] at *,
  set g := inv_fp ⟨-f,neg_posS hf⟩,
  intro m,
  specialize hC1 (-g m) (g m),
  simp only [df, add_left_neg] at hC1,
  rw [sub_eq_neg_add] at hC1,
  calc abs(f.1 (-g m) - I m) 
     = abs(f.1 0 + (-f.1 0 + f.1 (- g m) + f.1 (g m)) + (-f.1 (g m) - I m)) : by {ring_nf,ring_nf,ring_nf}
  ...≤ abs(f.1 0) + abs(-f.1 0 + f.1 (- g m) + f.1 (g m)) + abs(-f.1 (g m) - I m) : abs_add_three _ _ _
  ...≤ abs(f.1 0) + C1 + C2 : by {rw ←abs_neg (-f.val 0 + f.val (-g m) + f.val (g m)),simp only [neg_add_rev, neg_neg],
   rw tri3,linarith[hC2 m]},
end 

noncomputable instance (f : S) : decidable (f ∈ SP) := classical.dec (f ∈ SP)
noncomputable instance decfSN (f : S) : decidable (f ∈ SN) := classical.dec (f ∈ SN)
noncomputable instance decfS0 (f : S) : decidable (f ∈ S0) := classical.dec (f ∈ S0)

noncomputable def inv : S → S := λ f,
if hf : f ∈ SP then ⟨inv_fp ⟨f, hf⟩, l22 ⟨f, hf⟩⟩
else if hf : f ∈ SN then -⟨inv_fp ⟨-f, neg_posS hf⟩, l22 ⟨-f, neg_posS hf⟩⟩
else 0

lemma l23_f1 (f g : S) (ha : ∃ C, ∀ x, abs((-f + g).1 x) ≤ C) : f ∈ SP → g ∈ SN → false := 
begin
  intros hf hg,
  rcases ha with ⟨C,hC⟩,
  have hC1 : C + 1 > 0 := by linarith[hC 0,abs_nonneg ((-f + g).1 0)],
  rcases hf (C + 1) hC1 with ⟨N,hN⟩,
  rcases hg (C + 1) hC1 with ⟨M,hM⟩,
  specialize hC (max M N + 1),
  rw ←abs_neg at hC,
  simp at hC,
  rw ←subtype.val_eq_coe at hC,
  rw ←subtype.val_eq_coe at hC,
  have hN1 : max M N + 1 > N := by linarith[le_max_right M N],
  have hM1 : max M N + 1 > M := by linarith[le_max_left M N],
  have h1 : -g.1 (max M N + 1) + f.1 (max M N + 1) > 2 * C + 2, 
    linarith[hN (max M N + 1) hN1, hM (max M N + 1) hM1],
  rw abs_le at hC,
  cases hC,
  linarith,
end

lemma l23_f2 (f g : S) (ha : ∃ C, ∀ x, abs((-f + g).1 x) ≤ C) : f ∈ SP → g ∈ S0 → false := 
begin
  intros hf hg,
  rcases hg with ⟨B,hB⟩,  
  rcases ha with ⟨C,hC⟩,
  have hBC0 : B + C + 1 > 0 := by linarith[hC 0,abs_nonneg ((-f + g).1 0),hB 0,abs_nonneg (g.1 0)],
  rcases hf (B + C + 1) hBC0 with ⟨N,hN⟩,
  specialize hN (N + 1) (lt_add_one N),
  specialize hC (N + 1),
  rw ←abs_neg at hC,
  simp at hC,
  rw ←subtype.val_eq_coe at hC,
  rw ←subtype.val_eq_coe at hC,
  specialize hB (N + 1),
  rw abs_le at *,
  cases hB,
  have h1 : -g.1 (N + 1) + f.1 (N + 1) > C + 1,
    linarith,
  cases hC,
  linarith,
end

lemma l23_f3 (f g : S) (ha : ∃ C, ∀ x, abs((-f + g).1 x) ≤ C) : f ∈ SN → g ∈ S0 → false := 
begin
  intros hf hg,
  rcases hg with ⟨B,hB⟩,  
  rcases ha with ⟨C,hC⟩,
  have hBC0 : B + C + 1 > 0 := by linarith[hC 0,abs_nonneg ((-f + g).1 0),hB 0,abs_nonneg (g.1 0)],
  rcases hf (B + C + 1) hBC0 with ⟨N,hN⟩,
  specialize hN (N + 1) (lt_add_one N),
  specialize hC (N + 1),
  simp at hC,
  rw ←subtype.val_eq_coe at hC,
  rw ←subtype.val_eq_coe at hC,
  specialize hB (N + 1),
  rw abs_le at *,
  cases hB,
  have h1 : -g.1 (N + 1) + f.1 (N + 1) > C + 1,
    linarith,
  cases hC,
  linarith,
end

lemma l23_f4 (f : S) : f ∉ SP → f ∉ SN → f ∈ S0 := 
λ h1 h2, or.elim3 (hNP0 f) (λ h3,false.elim (h1 h3)) (λ h3, h3) (λ h3, false.elim (h2 h3))

@[simp] lemma l24 {f g : S} : (f + g).1 = f.1 + g.1 := rfl
@[simp] lemma l24_2 {f : S} : (-f).1 = -f.1 := rfl

lemma pre_l25 (f g : S) (hfg : ∃ C, ∀ x, abs((-f + g).1 x) ≤ C) (hf : f ∈ SP) (hg : g ∈ SP) :
∃ D, ∀ m, abs(f.1 (inv_fp ⟨f, hf⟩ m) - f.1 (inv_fp ⟨g, hg⟩ m)) < D := 
begin
  rcases inv_mul_one ⟨f,hf⟩ with ⟨C1,hC1⟩,
  rcases inv_mul_one ⟨g,hg⟩ with ⟨C2,hC2⟩,
  rcases hfg with ⟨C3,hC3⟩,
  use C1 + C2 + C3,
  intro m,
  specialize hC1 m,
  specialize hC2 m,
  specialize hC3 (inv_fp ⟨g,hg⟩ m),
  simp only [l24, l8, l7, l20] at *,
  rw ←abs_neg at hC2,
  simp only [neg_sub] at hC2,
  simp only [neg_add_eq_sub] at hC3,
  calc abs(f.1 (inv_fp ⟨f, hf⟩ m) - f.1 (inv_fp ⟨g, hg⟩ m)) = abs((f.1 (inv_fp ⟨f, hf⟩ m) - I m) + 
  (I m - g.1 (inv_fp ⟨g,hg⟩ m)) + (g.1(inv_fp ⟨g,hg⟩ m) - f.1 (inv_fp ⟨g,hg⟩ m))) : by {ring_nf,ring_nf,ring_nf}
 ... ≤ abs(f.1 (inv_fp ⟨f, hf⟩ m) - I m) + abs(I m - g.1 (inv_fp ⟨g,hg⟩ m)) + 
 abs(g.1(inv_fp ⟨g,hg⟩ m) - f.1 (inv_fp ⟨g,hg⟩ m)) : abs_add_three _ _ _
 ... < C1 + C2 + C3 : by linarith,
end

lemma l25 (f g : S) (hfg : ∃ C, ∀ x, abs((-f + g).1 x) ≤ C) (hf : f ∈ SP) (hg : g ∈ SP) :
∃ D, ∀ m, abs(-inv_fp ⟨f,hf⟩ m + inv_fp ⟨g,hg⟩ m) ≤ D := 
begin
  rcases pre_l25 f g hfg hf hg with ⟨C,hC⟩,
  cases f.2 with D hD,
  have h0 : ∃ D, ∀ m, abs(f.1 (-inv_fp ⟨f,hf⟩ m + inv_fp ⟨g,hg⟩ m)) < D,
    use C + D,
    intro m,
    specialize hD (inv_fp ⟨f,hf⟩ m) (-inv_fp ⟨f,hf⟩ m + inv_fp ⟨g,hg⟩ m),
    simp only [df] at hD,
    simp only [add_neg_cancel_left] at hD,
    specialize hC m,
    rw ←abs_neg,
    calc abs (-f.1 (-inv_fp ⟨f,hf⟩ m + inv_fp ⟨g,hg⟩ m)) 
       = abs((f.1 (inv_fp ⟨f, hf⟩ m) - f.1 (inv_fp ⟨g, hg⟩ m)) + (f.1 (inv_fp ⟨g, hg⟩ m) 
       - f.1 (inv_fp ⟨f, hf⟩ m) - f.1 (-inv_fp ⟨f, hf⟩ m + inv_fp ⟨g, hg⟩ m))) : by {ring_nf,ring_nf}
    ...≤ abs(f.1 (inv_fp ⟨f, hf⟩ m) - f.1 (inv_fp ⟨g, hg⟩ m)) + abs(f.1 (inv_fp ⟨g, hg⟩ m) 
         - f.1 (inv_fp ⟨f, hf⟩ m) - f.1 (-inv_fp ⟨f, hf⟩ m + inv_fp ⟨g, hg⟩ m)) : abs_add _ _
    ...< C + D : by linarith,
  have h1 : ∃ D, ∀ x ∈ {x : ℤ | ∃ m, x = -inv_fp ⟨f,hf⟩ m + inv_fp ⟨g,hg⟩ m}, 
    abs((⟨f,hf⟩ : SP).1.1 x) < D,  
    rcases h0 with ⟨D,hD⟩,
    use D,
    intros x hx,
    rcases hx with ⟨m,hm⟩,
    rw hm,
    exact hD m,
  rcases bdd_range ⟨f,hf⟩ h1 with ⟨D,hD⟩,
  use D - 1,
  intro m,
  set x := -inv_fp ⟨f,hf⟩ m + inv_fp ⟨g,hg⟩ m with hx,
  have hx1 : x ∈ {x : ℤ | ∃ m, x = -inv_fp ⟨f,hf⟩ m + inv_fp ⟨g,hg⟩ m}, 
    use m,
  specialize hD x hx1,
  have hD2 : abs x + 1 ≤ D := int.add_one_le_iff.mpr hD, 
  linarith,
end 

lemma l26 : (@has_equiv.equiv ↥S (@setoid_has_equiv ↥S (@quotient_add_group.left_rel ↥S S.to_add_group B)) ⇒
  @has_equiv.equiv ↥S (@setoid_has_equiv ↥S (@quotient_add_group.left_rel ↥S S.to_add_group B))) inv inv :=
begin
  intros f g hfg,
  simp only [inv],
  have h2 : ∃ C, ∀ x, abs((-g + f).1 x) ≤ C, 
    cases hfg with C hC, use C, rw l24, intro x, specialize hC x, rw ←abs_neg, simp at *, exact hC,
  split_ifs,
    { exact l25 f g hfg h h_1},
    { exfalso,
      exact l23_f1 f g hfg h h_2}, 
    { exfalso,
      exact l23_f2 f g hfg h (l23_f4 g h_1 h_2)},
    { exfalso,
    exact l23_f1 g f h2 h_2 h_1},
    { have h3 : ∃ C, ∀ x, abs((- -f + -g).1 x) ≤ C, 
      cases h2 with C hC, use C,intro x, specialize hC x, simp at *, rw add_comm,exact hC,
      rcases l25 (-f) (-g) h3 (neg_posS h_1) (neg_posS h_3) with ⟨C,hC⟩,
      use C,
      intro x,
      rw ←abs_neg,
      simp at *,
      rw add_comm,
      linarith[hC x]},
    { exfalso,
      exact l23_f3 f g hfg h_1 (l23_f4 g h_2 h_3)},
    { exfalso,
      exact l23_f2 g f h2 h_2 (l23_f4 f h h_1)},
    {exfalso,   
    exact l23_f3 g f h2 h_3 (l23_f4 f h h_1)},
    {refl},
end

lemma hf0 (f : S) : f ∈ S0 ↔ ⟦f⟧ = ⟦0⟧ := 
begin
  split,
    intro h,
    apply quotient.eq.mpr,
    rcases h with ⟨C,hC⟩,
    use C,
    simp only [add_zero, abs_neg, l7, l20],
    exact hC,
    intro h,
    rcases quotient.eq.mp h with ⟨C,hC⟩,
    simp at hC,
    use C,
    exact hC,
end

noncomputable def E.inv : 𝔼 → 𝔼 := quotient.map inv l26

noncomputable instance : field 𝔼 := 
{ inv := E.inv,
  exists_pair_ne := 
  begin
    use [0,1],
    norm_num,
    by_contradiction,
      have h1 : (1 : 𝔼) ∈ E'.P,
        use [⟨I,I_in_S⟩,rfl],
        intros C hC,
        use C,
        intros p hp,
        simp [I],
        exact hp,
      rw ←h at h1,
      exact E'.positive h1,
  end,
  mul_inv_cancel := 
  begin
    intros f hf,
    induction f, 
    work_on_goal 0 {
      dsimp at *, 
      apply quotient.eq.mpr,
      simp only [S.mul,inv],
      split_ifs,
        {rcases inv_mul_one ⟨f,h⟩ with ⟨C,hC⟩,
        use C + 1,
        intro x,
        rw ←abs_neg,
        simp at *,
        rw add_comm,
        ring_nf,
        linarith[hC x]},
        {rcases inv_mul_one.neg f h_1 with ⟨C,hC⟩,
        use C,
        intro x,
        rw [←abs_neg,add_comm],
        simp at *,
        ring,
        linarith [hC x]},
        {exfalso,
        have hfS0 : f ∈ S0 := l23_f4 f h h_1,
        rw hf0 at hfS0,
        exact hf hfS0},}, 
    refl,
  end,
  inv_zero := 
  begin
    apply quotient.eq.mpr,
    simp [inv],
    have h0 : (0 : S) ∈ S0 := B.zero_mem',
    split_ifs,
    {exfalso,
     exact l9_exclusive_12 S.zero_mem' h0 h},
    {exfalso,
     exact l9_exclusive_13 S.zero_mem' h0 h_1},
    {refl,},
  end,
    ..𝔼.comm_ring}

lemma pos_one : (1 : 𝔼) ∈ E'.P := 
begin
  use [⟨I,I_in_S⟩,rfl],
  intros C hC,
  use C,
  intros p hp,
  simp [I],
  exact hp,
end

noncomputable instance : linear_ordered_field 𝔼 := 
{ add_le_add_left := 
  begin
    intros f g hfg h,
    cases hfg with h1 h2,
    apply or.intro_left,
    simp,
    exact h1,
    apply or.intro_right,
    simp,
    exact h2,
  end,
  mul_pos := 
  begin 
    intros f g hf hg,
    rcases hf with ⟨f',hf',hC1⟩,
    rcases hg with ⟨g',hg',hC2⟩,
    have h1 : ↑(S.mul f' g') =  mul f g - 0, 
      simp at *,
      have : ↑(S.mul f' g') = mul ↑f' ↑g' := rfl,
      rw [hf',hg'] at this,
      exact this,
    use [S.mul f' g',h1],
    simp at *,
    intros C hC,
    rcases hC1 C hC with ⟨N,hN⟩,
    have hN1 : max N 1 > 0 := by linarith[le_max_right N 1],
    rcases hC2 (max N 1) hN1 with ⟨M,hM2⟩,
    use M,
    intros p hp,
    simp [S.mul],
    exact hN ((↑g' : G) p) (by linarith[(hM2 p hp),le_max_left N 1]),
  end,
  zero_le_one := 
  begin
    have h0 : (0: 𝔼) < 1,
     have h1 : ((1 : 𝔼) - 0) ∈ E'.P, simp, exact pos_one,
     exact h1,
    exact le_of_lt h0,
  end,
    ..𝔼.linear_order,
    ..𝔼.field} 

lemma int_in_S {A : ℤ} : (λ x, A * x) ∈ S := 
begin
  use 5,
  intros p q,
  simp [df],
  ring_nf,
  norm_num,
end

lemma int_infinite : ∀ B C : ℤ, ∃ N, ∀ x > N, x - B > C := 
begin
  intros B C,
  use B + C,
  intros x hx,
  linarith,
end

def 𝔼.int : ℤ → 𝔼 := λ A, quotient_add_group.mk ⟨(λ x, A * x),int_in_S⟩

lemma 𝔼.zero_zero : 𝔼.int 0 = 0 := 
begin
  simp [𝔼.int],
  apply quotient.eq.mpr,
  use 5,
  intro x,
  simp,
  norm_num,
end

@[simp] lemma 𝔼.one_one : 𝔼.int 1 = 1 := 
begin
  simp [𝔼.int],
  apply quotient.eq.mpr,
  use 5,
  intro x,
  simp [I],
  norm_num,
end

lemma increasing_𝔼.int : ∀ B C : ℤ, B > C → 𝔼.int B > 𝔼.int C := 
begin
  intros B C hBC,
  use [⟨λ x, B * x, int_in_S⟩ - ⟨λ x, C * x, int_in_S⟩,rfl],
  intros C1 hC1,
  have hBC0 : B - C > 0, linarith,
  use C1 / (B - C),
  intros p hp,
  rw ←tactic.ring.add_neg_eq_sub,
  simp,
  have h1 : p * (B - C)  > C1 := int.lt_mul_of_div_lt hBC0 hp, 
  linarith,
end

@[simp] lemma homo_int_mul (C D : ℤ): 𝔼.int (C * D) = (𝔼.int C) * (𝔼.int D) := 
begin
  simp [𝔼.int,mul],
  apply quotient.eq.mpr,
  simp [S.mul],
  simp,
  use 1,
  simp,
  intro x,
  rw mul_assoc,
  simp,
end 

@[simp] lemma homo_int_add (C D : ℤ): 𝔼.int (C + D) = (𝔼.int C) + (𝔼.int D) := 
begin
  simp [𝔼.int],
  apply quotient.eq.mpr,
  use 11,
  intro x,
  simp,
  ring_nf,
  simp,
  norm_num,
end

@[simp] lemma epos(a: ℤ):a>0 → (↑a:  𝔼) > 0 := int.cast_pos.mpr

@[simp] lemma emin (f g: S) :(↑(g - f) : 𝔼) = ↑g - ↑f:= rfl

lemma archi1 : ∀ x : 𝔼, ∃ M > 0, x < 𝔼.int M := 
begin
  intro x,
  rcases quotient.exists_rep x with ⟨z,hz⟩,
  have hz1 :  ↑z = x := hz,
  rcases l15 z.2 with ⟨A,B,hA⟩,
  use [max (A + 1) 1, by linarith[le_max_right (A + 1) 1]],
  set Ax : ↥S := ⟨(λ x, (max (A + 1) 1) * x),int_in_S⟩ with hAx,
  use Ax - z,
    have h1 : (↑(Ax - z) : 𝔼) = ↑Ax - ↑z := by simp,
    split,
    simp [𝔼.int],
    rw [hz1],
    simp,
    refl,
    intros C hC,
    rcases int_infinite B C with ⟨N,hN⟩,
    use max (N + 1) 0,
    intros p hp,
    specialize hA p,
    have hp0 : p > 0 := by linarith[le_max_right (N + 1) 0,hp],
    have hpN : p > N := by linarith[le_max_left (N + 1) 0,hp],
    rw [abs_of_pos hp0,abs_lt] at hA,
    cases hA,
    rw ←tactic.ring.add_neg_eq_sub,
    simp only [l24,l8, l7, l20],
    calc max (A + 1) 1 * p + - z.1 p 
       > max(A + 1) 1 * p - (A * p + B) : by linarith
   ... = (max(A + 1) 1 - A) * p - B : by ring
   ... ≥ (A + 1 -A) * p - B : by linarith[(mul_le_mul_right hp0).mpr (le_max_left (A + 1) 1)]
   ... = p - B : by ring
   ... > C : hN p hpN,
end

lemma archi2 : ∀ (x y : 𝔼)(hy : y > 0), ∃ M > 0, x < 𝔼.int M * y := 
begin  
  intros x y hy,
  rcases archi1 x with ⟨C,hC0,hC⟩,
  rcases archi1 y⁻¹ with ⟨D,hD0,hD⟩,
  set C1 := max (C + 1) 1 with hC1,
  use [C1 * D,mul_pos (by linarith[le_max_right (C + 1) 1]) hD0],
  have h2 : 𝔼.int C1 > 0, 
    rw ←𝔼.zero_zero, 
    apply increasing_𝔼.int C1 0 (by linarith [le_max_right (C + 1) 1]),
  have h3 : 𝔼.int C1 * y > 0 := mul_pos h2 hy,
  have h4 : y⁻¹ > 0 := inv_pos.mpr hy,
  simp,
  rw [mul_assoc,mul_comm (𝔼.int D) y,←mul_assoc],
    calc x < 𝔼.int C1 : by {rw hC1,linarith[hC,increasing_𝔼.int 
      (max (C + 1) 1) C (by linarith[le_max_left (C + 1) 1])]}
      ...= (𝔼.int C1) * 1 : by simp
      ...= 𝔼.int C1 * (y * y⁻¹) : by rw mul_inv_cancel (ne_of_gt hy)
      ...= 𝔼.int C1 * y * y⁻¹  : by rw mul_assoc
      ...< 𝔼.int C1 * y * (𝔼.int D) : (mul_lt_mul_left h3).mpr hD,
end

lemma l27 : 𝔼.int ∘ int.of_nat = nat.cast := 
begin
  ext,
  induction x with n hn,
    simp,
    rw 𝔼.zero_zero,
    refl,
    simp at *,
    have h1 : (n.succ.cast : 𝔼) = n.cast + 1 := rfl,
    rw h1,
    simp,
    exact hn,
end 

instance : archimedean 𝔼 := 
{ arch :=
    begin
      intros x y hy,
      rcases archi2 x y hy with ⟨M,hM0,hM⟩,
      rcases (int.eq_coe_of_zero_le (le_of_lt hM0)) with ⟨N,hN⟩,
      cases hN, 
      use N,
      simp,
      unfold_coes,
      have h1 : 𝔼.int (int.of_nat N) = nat.cast N,
        exact (congr_fun (eq.symm l27) N).symm.congr_right.mp rfl,
      rw ←h1,
      simp,
      rw ←hN,
      exact (le_of_lt) hM,
    end}

lemma archi3 : ∀ (x y : 𝔼)(hxy : x < y), ∃ (M N : ℤ)(h : N > 0), x < M / N 
∧ ↑M / ↑N < y :=
begin
  intros x y hxy,
  rcases exists_rat_btwn hxy with ⟨q,hq⟩,
  use [q.num, ↑(q.denom),int.coe_nat_pos.mpr q.pos],
  simp,
  exact hq,
end

noncomputable instance : floor_ring 𝔼 := archimedean.floor_ring 𝔼

noncomputable def 𝔼.floor := 𝔼.floor_ring.floor

lemma almost_homo_floor (x y : 𝔼) : 0 ≤ 𝔼.floor (x + y) - 𝔼.floor x - 𝔼.floor y 
∧ 𝔼.floor (x + y) - 𝔼.floor x - 𝔼.floor y < 2 := 
begin
  have hx0 : x - floor x ≥ 0 := by linarith[floor_le x],
  have hx1 : x - floor x < 1 := by linarith[lt_floor_add_one x],
  have hy0 : y - floor y ≥ 0 := by linarith[floor_le y],
  have hy1 : y - floor y < 1 := by linarith[lt_floor_add_one y],
  have hxy0 : x + y - floor x - floor y ≥ 0 := by linarith,
  have hxy2 : x + y - floor x - floor y < (↑2 : 𝔼) := by {simp, linarith},
  have hxy0f : floor( x + y - floor x - floor y) ≥ floor (0 : 𝔼) := floor_mono hxy0,
  have hxy2f : floor( x + y - floor x - floor y) < 2 := floor_lt.mpr hxy2,
  rw sub_sub at hxy0f,
  rw sub_sub at hxy2f,
  rw ←int.cast_add at *,
  rw floor_sub_int (x + y) (floor x + floor y) at hxy0f,
  rw floor_sub_int (x + y) (floor x + floor y) at hxy2f,
  simp only [nat.cast_bit0, ge_iff_le, floor_zero, nat.cast_one,sub_sub] at *,
  exact and.intro hxy0f hxy2f,
end

noncomputable instance i (p : ℤ)(S : set 𝔼) : decidable_pred (λ (n : ℕ), ∀ (x : 𝔼), x ∈ S → ↑n > (↑p * x).floor):=
classical.dec_pred (λ (n : ℕ), ∀ (x : 𝔼), x ∈ S → ↑n > (↑p * x).floor)

lemma enonneg(a: ℤ): a ≥ 0 → (↑a: 𝔼) ≥ 0:= int.cast_nonneg.mpr

lemma pos_set_max (T : set 𝔼) [nonempty T] (hT : ∃ X, ∀ x ∈ T, x < X): ∀ (p : ℤ) (hp : p ≥ 0), 
 ∃ n ≥ 0, (∀ x ∈ T, n > 𝔼.floor (p * x)) ∧ ∀ m ≥ 0, m < n → ∃ x ∈ T, m ≤ 𝔼.floor (p * x) :=
begin
  intros p hp,
  have h1 : ∃ n : ℕ, ∀ x ∈ T, ↑n > 𝔼.floor (p * x), 
    rcases hT with ⟨X,hX⟩,
    rcases int.eq_coe_of_zero_le (le_max_right ((↑p * X).floor + 1) 0) with ⟨n,hn⟩,
    use n,
    intros x hx,
    specialize hX x hx,
    have h2 : (↑p : 𝔼) ≥ 0 := enonneg p hp,
    have h3 : (↑p : 𝔼) * x ≤ ↑p * X,
      by_cases hp2 : (↑p : 𝔼) > 0,
      exact le_of_lt ((mul_lt_mul_left hp2).mpr hX),
      have hp0 : (p : 𝔼)  = 0 := le_antisymm (not_lt.mp hp2) h2,
      simp [hp0],
    have h4 : (↑p * x).floor ≤ (↑p * X).floor := floor_mono h3,
    linarith[le_max_left ((↑p * X).floor + 1) 0],
  rcases (nat.find_x h1) with ⟨n,hn⟩,
  use [↑n,int.coe_zero_le n],
  simp only [] at hn,
  cases hn with hn1 hn2,
  split,
    exact hn1,
    intros m hm hmn,
    rcases (int.eq_coe_of_zero_le hm) with ⟨m',hm'⟩,
    rw hm' at hmn,
    rw hm',
    simp at *,
    exact hn2 m' hmn,
end

noncomputable
instance j (p : ℤ)(S : set 𝔼) : decidable_pred (λ (n : ℕ), ∃ (x : 𝔼) (H : x ∈ S), ↑n = -(↑p * x).floor)
:= classical.dec_pred (λ (n : ℕ), ∃ (x : 𝔼) (H : x ∈ S), ↑n = -(↑p * x).floor)

lemma neg_set_max (T : set 𝔼) [nonempty T] (hT : ∃ X, ∀ x ∈ T, x < X): ∀ (p : ℤ) (hp : p ≥ 0) (hpx : ∀ x ∈ T, 
𝔼.floor (p * x) < 0), ∃ n, (∃ x ∈ T, n = 𝔼.floor (p * x)) ∧ ∀ m, m > n → ∀ x ∈ T, m ≠ 𝔼.floor (p * x) :=
begin
  intros p hp hpx,
  have h1 : ∃ n : ℕ, ∃ x ∈ T, ↑n = -𝔼.floor (↑p * x),
    rcases nonempty_subtype.mp _inst_1 with ⟨x,hx⟩,
    rcases int.eq_coe_of_zero_le (le_of_lt (neg_pos.mpr (hpx x hx))) with ⟨n,hn⟩,
    use [n,x,hx],
    exact hn.symm,
  rcases (nat.find_x h1) with ⟨n,hn⟩,
  simp at *,
  cases hn with hn1 hn2,
  use -↑n,
  split,
    rcases hn1 with ⟨x,hxT,hx⟩,
    use [x,hxT],
    exact neg_eq_iff_neg_eq.mp (eq.symm hx),
    intros m hm x hx,
    by_cases hm0 : m ≥ 0,
      by_contradiction,
      linarith[hpx x hx],
      simp at hm0,
      rcases int.lt.dest hm0 with ⟨l,hm'⟩,
      set m' := l.succ,
      have hm'm : m = -↑m' := eq_neg_of_add_eq_zero hm',
      rw hm'm at hm, 
      specialize hn2 m' (int.lt_of_coe_nat_lt_coe_nat (neg_lt_neg_iff.mp hm)) x hx,
      by_contradiction,
      rw hm'm at h,
      exact hn2 (eq_neg_of_eq_neg (eq.symm h)),
end

lemma set_max (T : set 𝔼) [nonempty T] (hT : ∃ X, ∀ x ∈ T, x < X) : ∀ (p : ℤ) (hp : p ≥ 0), 
 ∃ n, (∃ x ∈ T, n = 𝔼.floor (p * x)) ∧ ∀ m, m > n → ∀ x ∈ T, m ≠ 𝔼.floor (p * x) := 
begin
  intros p hp,
  rcases pos_set_max T hT p hp with ⟨n,hn0,hn⟩,
  cases hn with hn1 hn2,
  by_cases hn0' : n > 0,
    use (n - 1),
    have hn10 : n - 1 ≥ 0 := int.le_sub_one_iff.mpr hn0',
    rcases hn2 (n - 1) hn10 (by linarith) with ⟨x,hxS,hx⟩,
    use [x, hxS,le_antisymm hx (int.le_sub_one_iff.mpr (hn1 x hxS))],
    intros m hm y hy,
    specialize hn1 y hy,
    exact ne_of_gt (by linarith[int.le_sub_one_iff.mpr hn1]),
    have h1 : ∀ x ∈ T, 𝔼.floor (p * x) < 0, 
      intros x hx,
      linarith[hn1 x hx,not_lt.mp hn0'],
    exact neg_set_max T hT p hp h1,
end

noncomputable def Sup_f (T : set 𝔼)[nonempty T](hT : ∃ X, ∀ x ∈ T, x < X) : G := λ p, 
if hp : p ≥ 0 then 
begin
  choose n hn using set_max T hT p hp,
  exact n,
end
else 
begin
  choose n hn using set_max T hT (-p) (le_of_lt (neg_pos.mpr (not_le.mp hp))),
  exact -n,
end

lemma Sup_f.neg (T : set 𝔼)[nonempty T](hT : ∃ X, ∀ x ∈ T, x < X) : ∀ p < 0, (Sup_f T hT) (p) = -(Sup_f T hT) (-p) :=
begin
  intros p hp,
  simp only [Sup_f],
  split_ifs,
  exfalso,
    linarith,
  simp,
  exfalso,
    linarith,
end

lemma max_in_T {T : set 𝔼}(a b c : 𝔼)(ha : a ∈ T)(hb : b ∈ T)(hc : c ∈ T) : max a (max b c) ∈ T :=
begin
  by_cases h1 : a > max b c,
    rw max_eq_left_of_lt h1,
    exact ha,
    rw max_eq_right (not_lt.mp h1),
    by_cases h2 : b > c,
    rw max_eq_left_of_lt h2,
    exact hb,
    rw max_eq_right (not_lt.mp h2),
    exact hc,    
end 

lemma Sup_in_S (T : set 𝔼)[nonempty T](hT : ∃ X, ∀ x ∈ T, x < X) : (Sup_f T hT) ∈ S :=
begin
  apply l18,
  apply Sup_f.neg,
  use 2,
  intros m n hm hn,
  simp only [df,Sup_f],
  split_ifs,
    have h1 := classical.some_spec (set_max T hT m hm),
    set m' :=  classical.some (set_max T hT m hm) with hm',
    have h2 :=  classical.some_spec (set_max T hT n hn),
    set n' :=  classical.some (set_max T hT n hn) with hn',
    have h3 :=  classical.some_spec (set_max T hT (m + n) h),
    set mn' :=  classical.some (set_max T hT (m + n) h) with hmn',
    cases h1 with h11 h12,
    cases h2 with h21 h22,
    cases h3 with h31 h32,
    rcases h11 with ⟨x,hxT,hx⟩,
    rcases h21 with ⟨y,hyT,hy⟩,
    rcases h31 with ⟨z,hzT,hz⟩,
    rw ←hm' at *,
    rw ←hn' at *,
    rw ←hmn' at *,
    let xmax := max x (max y z),
    have h41 : m' = (↑m * xmax).floor,
      apply le_antisymm,
      have h5 : xmax ≥ x, linarith[le_max_left x (max y z)],
      have h6 : (↑m : 𝔼) ≥ 0 :=  enonneg m hm,
      have h7 : ⌊↑m * xmax⌋ ≥ (↑m * x).floor := floor_mono(mul_le_mul_of_nonneg_left h5 h6), 
      rw ←hx at h7,
      exact h7,
      specialize h12 (↑m * xmax).floor,
      by_contradiction,
      have := h12 (not_le.mp h), 
      specialize this xmax (max_in_T x y z hxT hyT hzT),
      exact this rfl,
    have h42 : n' = (↑n * xmax).floor,
      apply le_antisymm,
      have h5 : xmax ≥ y, linarith[le_max_right x (max y z),le_max_left y z],
      have h6 : (↑n : 𝔼) ≥ 0 := enonneg n hn,
      have h7 : ⌊↑n * xmax⌋ ≥ (↑n * y).floor := floor_mono(mul_le_mul_of_nonneg_left h5 h6), 
      rw ←hy at h7,
      exact h7,
      specialize h22 (↑n * xmax).floor,
      by_contradiction,
      have := h22 (not_le.mp h), 
      specialize this xmax (max_in_T x y z hxT hyT hzT),
      exact this rfl,
     have h43 : mn' = (↑(m + n) * xmax).floor,
      apply le_antisymm,
      have h5 : xmax ≥ z, linarith[le_max_right x (max y z),le_max_right y z],
      have h6 : (↑(m + n) : 𝔼) ≥ 0 := enonneg (m+n) h,
      have h7 : ⌊↑(m + n) * xmax⌋ ≥ (↑(m + n) * z).floor := floor_mono(mul_le_mul_of_nonneg_left h5 h6), 
      rw ←hz at h7,
      exact h7,
      specialize h32 (↑(m + n) * xmax).floor,
      by_contradiction,
      have := h32 (not_le.mp h), 
      specialize this xmax (max_in_T x y z hxT hyT hzT),
      exact this rfl,
    rw [h41,h42,h43,int.cast_add,add_mul],
    have := almost_homo_floor (↑m * xmax) (↑n * xmax),
    rw abs_lt,
    cases this,
    split,
      linarith,
      linarith,
  simp at h,
  linarith,
end

noncomputable instance k (T : set 𝔼) : decidable (nonempty T ∧ ∃ (X : 𝔼), ∀ (x : 𝔼), 
x ∈ T → x < X) :=  classical.dec (nonempty ↥T ∧ ∃ (X : 𝔼), ∀ (x : 𝔼), x ∈ T → x < X)
noncomputable instance l (T : set 𝔼) : decidable (∃ (x : 𝔼) (H : x ∈ T), ∀ (y : 𝔼), 
y ∈ T → y ≤ x) := classical.dec (∃ (x : 𝔼) (H : x ∈ T), ∀ (y : 𝔼), y ∈ T → y ≤ x)

noncomputable def 𝔼.Sup : set 𝔼 → 𝔼 := λ T,
if hT1 : nonempty T ∧ ∃ X, ∀ x ∈ T, x < X then
  if hT2 : ∃ x ∈ T, ∀ y ∈ T, y ≤ x then
    begin 
      choose x hx using hT2,
      exact x,
    end
  else  
    begin
      haveI : nonempty T := hT1.1,
      exact quotient_add_group.mk ⟨(Sup_f T hT1.2),Sup_in_S T hT1.2⟩,
    end 
else 0 

lemma N_Sup_f_in_S (T : set 𝔼) [nonempty T](hT : ∃ X, ∀ x ∈ T, x < X) : 
∀ (N > 0), (λ p, (⟨Sup_f T hT,Sup_in_S T hT⟩ : S).1 (p * N)) ∈ S :=
begin
  intros N hN,
  simp,
  rcases Sup_in_S T hT with ⟨C,hC⟩,
  use C,
  intros p q,
  simp [df] at *,
  specialize hC (p * N) (q * N),
  rw add_mul,
  exact hC, 
end 

lemma int_negone_negone : 𝔼.int (-1) = (-1 : ℤ).cast := 
begin
  simp [𝔼.int],
  apply quotient.eq.mpr,
  use 1,
  intro x,
  simp [I],
end

lemma l28 : 𝔼.int = int.cast := 
begin
  ext,
  induction x with n n',
    induction n with m hm,
      simp,
      rw 𝔼.zero_zero,
      refl,
      simp at *,
      have h1 : (((↑m : ℤ) + 1).cast : 𝔼) = (↑m : ℤ).cast + 1 := rfl,
      rw [h1,hm],
    induction n' with m hm,
      rw int.neg_succ_of_nat_coe,
      simp,
      exact int_negone_negone,
      rw int.neg_succ_of_nat_coe at *,
      simp at *,
      have h1 : -1 + -(↑m : ℤ) = -(1 + ↑m) := by {simp,ring_nf,ring_nf}, 
      have h2 : (((-1 + -(1 + (↑m : ℤ))).cast) : 𝔼) = (-1 : ℤ).cast - (1 + (↑m : ℤ)).cast,
        have := int.cast_sub,
        unfold_coes at this,
        rw ←this,
        ring,
      have h3 := int.cast_neg,
      unfold_coes at h3,
      rw [←neg_add,h3] at hm,
      rw [h1,h2,hm,int_negone_negone],
      ring,
end

lemma l29 (f g : S) : (↑f : 𝔼) * ↑g = ↑(S.mul f g) := rfl
lemma l30 (a : ℤ) : 𝔼.int a = ↑(⟨(λ x,a * x),int_in_S⟩ : S) := rfl
lemma l31 (T : set 𝔼)[nonempty T](hT1 :  ∃ X, ∀ x ∈ T, x < X) (hT2 : ¬∃ x ∈ T, ∀ y ∈ T, y ≤ x)
: 𝔼.Sup T = ↑(⟨(Sup_f T hT1),Sup_in_S T hT1⟩ : S) :=
begin
  simp only [𝔼.Sup],
  split_ifs,
    refl,
    exfalso,
    simp at h,
    rcases nonempty_subtype.mp _inst_1 with ⟨x,hx⟩,
    rcases hT1 with ⟨B,hB⟩,
    rcases h (nonempty_of_mem hx) B with ⟨y,hyT,hy⟩,
    linarith[hB y hyT],
end

lemma almost_homo_Sup_f (T : set 𝔼) [nonempty T](hT : ∃ X, ∀ x ∈ T, x < X) : 
∀ (N : ℤ)(H : N > 0), 
(↑(⟨(λ p, (⟨Sup_f T hT,Sup_in_S T hT⟩ : S).1 (p * N)),N_Sup_f_in_S T hT N H⟩ : S) : 𝔼) =
(↑(⟨Sup_f T hT,Sup_in_S T hT⟩ : S) : 𝔼) * ↑N := 
begin
  intros N hN,
  unfold_coes,
  rw [←l28,l30 N],
  apply quotient.eq.mpr,
  simp [S.mul],
  use 10,
  simp,
  intro x,
  rw mul_comm,
  norm_num,
end 

lemma l32 (f g : S) (hfg : ∀ p > 0, f.1 p ≥ g.1 p) : (↑f : 𝔼) ≥ ↑g :=
begin
  have h1 : ¬ (↑f : 𝔼) < ↑g,
    by_contradiction,
      rcases h with ⟨f',hf',hf'2⟩,
      rw ←emin at hf',
      have h3 : ⟦g - f⟧ = ⟦f'⟧ := hf'.symm,
      rcases quotient.eq.mp h3 with ⟨B,hB⟩,
      simp only [l24, gt_iff_lt, l8, ge_iff_le, neg_sub] at *,
      have h4 : B ≥ 0 := by linarith[abs_nonneg ((f - g).1 0 + f'.1 0),hB 0],
      specialize hf'2 (B + 1) (by linarith),
      rcases hf'2 with ⟨N,hN⟩,  
      specialize hB (max (N + 1) 1),
      rw abs_le at hB,
      cases hB with hB1 hB2,
      specialize hfg (max (N + 1) 1) (by linarith[le_max_right (N + 1) 1]),
      rw ←sub_nonneg at hfg,
      rw ←tactic.ring.add_neg_eq_sub at hB2,
      simp only [l24, l8, l7, l24_2] at hB2,
      ring_nf at hB2,
      set l := f.1 (max (N + 1) 1) - g.1 (max (N + 1) 1) with hl,
      rw ←hl at *,
      have : f'.1(max (N + 1) 1) < B + 1 - l := lt_sub_iff_add_lt'.mpr (int.lt_add_one_iff.mpr hB2),
      linarith[sub_le_self (B + 1) hfg,hN (max (N + 1) 1) (by linarith[le_max_left (N + 1) 1])],
  exact not_lt.mp h1, 
end

lemma l33 {f g : S} (hfg : (↑f : 𝔼) < ↑g) : ∃ p > 0, f.1 p < g.1 p := 
begin
  rcases hfg with ⟨f',hf',hf'2⟩,
  rw ←emin at hf',
  have h3 : ⟦g - f⟧ = ⟦f'⟧ := hf'.symm,
  rcases quotient.eq.mp h3 with ⟨B,hB⟩,
  simp only [l24, gt_iff_lt, l8, ge_iff_le, neg_sub] at *,
  have h4 : B ≥ 0 := by linarith[abs_nonneg ((f - g).1 0 + f'.1 0),hB 0],
  specialize hf'2 (B + 1) (by linarith),
  rcases hf'2 with ⟨N,hN⟩,  
  specialize hB (max (N + 1) 1),
  rw abs_le at hB,
  cases hB with hB1 hB2,
  use [max (N + 1) 1,(by linarith[le_max_right (N + 1) 1])],
  specialize hN (max (N + 1) 1) (by linarith[le_max_left (N + 1) 1]),
  have hB3 : (f - g).1 (max (N + 1) 1) + (B + 1) < B,
    calc (f - g).1 (max (N + 1) 1) + (B + 1) < (f - g).1 (max (N + 1) 1) + f'.1 (max (N + 1) 1) : by linarith
                                         ... ≤ B : hB2,
  have : (f - g).1 (max (N + 1) 1) < 0, linarith,
  rw ←tactic.ring.add_neg_eq_sub at this,
  simp only [l24, l8, l7, l24_2] at this,
  linarith,
end

lemma le_cSup' (T : set 𝔼)(hT : bdd_above T): ∀ x ∈ T, x ≤ 𝔼.Sup T :=
begin
  intros x hx,
  simp only [𝔼.Sup],
  split_ifs with hT2 hT3,
    {cases classical.some_spec hT3,
    exact h x hx},
    {simp at hT3,
    rcases hT3 x hx with ⟨y,hyT,hxy⟩,
    rcases archi3 x y hxy with ⟨M,N,hN,hMN1,hMN2⟩,
    haveI : nonempty T := hT2.1,
    have h1 : ∀ p > 0, (⟨Sup_f T hT2.2,Sup_in_S T hT2.2⟩ : S).1 (p * N) ≥ p * M,
      intros p hp,
      have h2 : ¬(⟨Sup_f T hT2.2,Sup_in_S T hT2.2⟩ : S).1 (p * N) < ⌊((↑(p * N) : 𝔼) * y)⌋,
        simp only [Sup_f],
        split_ifs,
          by_contradiction,
          have h1 := classical.some_spec (set_max T hT2.2 (p * N) (le_of_lt (mul_pos hp hN))),
          cases h1 with h11 h12,
          specialize h12 ((↑(p * N) : 𝔼) * y).floor h y hyT,
          exact h12 rfl,
          exfalso,
          simp at h,
          linarith[mul_pos hp hN],
      have h3 : ⌊((↑(p * N) : 𝔼) * (↑M /↑N))⌋ ≤ ⌊((↑(p * N) : 𝔼) * y)⌋,
        exact floor_mono (le_of_lt 
             ((mul_lt_mul_left (epos (p*N) (mul_pos hp hN))).mpr hMN2)),
      simp at h3,
      ring_nf at h3,
      rw mul_comm (↑N)⁻¹ ↑M at h3,
      rw mul_assoc ↑M (↑N)⁻¹ ↑N at h3,
      have hN' : (↑N : 𝔼) > 0 := epos N hN,
      rw inv_mul_cancel (ne_of_gt hN') at h3,
      simp at h3,
      rw ←int.cast_mul at h3,
      rw floor_coe (M * p) at h3,
      simp at h2,
      ring_nf at h2,
      rw [mul_comm p N,mul_comm p M],
      linarith,
    have h2 : M.cast ≤ 
    (↑(⟨(λ p, (⟨Sup_f T hT2.2,Sup_in_S T hT2.2⟩ : S).1 (p * N)),N_Sup_f_in_S T hT2.2 N hN⟩ : S) : 𝔼),
      rw ←l28,
      rw l30,
      apply l32,
      simp at *,
      intros p hp,
      linarith[h1 p hp],
    rw almost_homo_Sup_f T hT2.2 at h2,
    have h3 : M.cast / (N.cast : 𝔼) ≤ (↑(⟨Sup_f T hT2.2,Sup_in_S T hT2.2⟩ : S) : 𝔼),
      exact (div_le_iff (int.cast_pos.mpr hN)).mpr h2,
    unfold_coes at *,
    linarith},
    exfalso,
    simp at hT2,
    specialize hT2 (nonempty_of_mem hx), 
    rcases hT with ⟨B,hB⟩,
    rw mem_upper_bounds at hB,
    rcases hT2 (B + 1) with ⟨x,hx,hxT⟩,
    linarith[hB x hx],
end

lemma cSup_le'' (T : set 𝔼)[nonempty T] : ∀ a ∈ upper_bounds T, 𝔼.Sup T ≤ a := 
begin
  intros a ha,
  simp only [𝔼.Sup],
  split_ifs with hT2 hT3,
  {cases classical.some_spec hT3,
    exact (mem_upper_bounds.mp ha) _ w},
  {have hf : ¬a < 𝔼.Sup T,
    by_contradiction has,
    rcases archi3 a (𝔼.Sup T) has with ⟨M,N,hN,hMN1,hMN2⟩,
    have h1 : (↑M : 𝔼) < (𝔼.Sup T) * N := (div_lt_iff (epos N hN)).mp hMN2,
    rw l31 T hT2.2 hT3 at h1,
    rw ←(almost_homo_Sup_f T hT2.2 N hN) at h1,
    unfold_coes at h1,
    rw [←l28,l30] at h1,
    rcases l33 h1 with ⟨p,hp0,hp⟩,
    simp at hp,
    have h2 : ∃ x ∈ T, Sup_f T hT2.2 (p * N) = ((↑(p * N) * x : 𝔼)).floor,
      simp only [Sup_f],
      split_ifs,
      have h3 := classical.some_spec (set_max T hT2.2 (p * N) (le_of_lt (mul_pos hp0 hN))),
      rcases h3.1 with ⟨x,hxT,hx⟩,
      use [x,hxT],
      exact hx,
      exfalso,
      exact h (le_of_lt (mul_pos hp0 hN)),
    rcases h2 with ⟨x,hxT,hx⟩,
    have h3 : ↑N * a < ↑M, 
      rw mul_comm, 
      exact (lt_div_iff (epos N hN)).mp hMN1,
    have hp0' : (↑p : 𝔼) > 0 := epos p hp0,
    have hpN : (↑p : 𝔼) * ↑N > 0 := mul_pos hp0' (int.cast_pos.mpr hN),
    have h4 : ↑p * ↑N * a < ↑p * ↑M, 
      rw mul_assoc, 
      exact (mul_lt_mul_left hp0').mpr h3,
    rw mem_upper_bounds at ha,
    have h5 : ↑p * ↑N * x ≤ ↑p * ↑N * a := (mul_le_mul_left hpN).mpr (ha x hxT),
    have h6 : ↑p * ↑N * x < ↑p * ↑M := by linarith,
    rw [←int.cast_mul,←int.cast_mul] at h6,
    have h7 : (↑(p * N) * x).floor ≤ ⌊((↑(p * M): 𝔼))⌋  := floor_mono (le_of_lt h6),
    rw [←hx,floor_coe (p * M)] at h7,
    linarith,
  rw l31 T hT2.2 hT3 at hf,
  exact not_lt.mp hf},
  { simp at hT2,
    rcases nonempty_subtype.mp _inst_1 with ⟨x,hx⟩,
    rcases hT2 (nonempty_of_mem hx) (a + 1)  with ⟨x,hxT,hx⟩,
    rw mem_upper_bounds at ha,
    specialize ha x hxT,
    linarith},
end 

lemma l34 {T : set 𝔼}(a : 𝔼)(ha : a ∈ lower_bounds T) : -a ∈ upper_bounds {x | -x ∈ T} := 
begin
  rw mem_lower_bounds at ha,
  intros x hx,
  specialize ha (-x) hx,
  linarith,
end

lemma l35 {T : set 𝔼}(hT : bdd_below T) : bdd_above {x | -x ∈ T} := 
begin
  rcases hT with ⟨a,ha⟩,
  use [-a,l34 a ha],
end

noncomputable def 𝔼.Inf : set 𝔼 → 𝔼 := λ T, -𝔼.Sup {x | -x ∈ T} 

noncomputable instance : lattice 𝔼 := distrib_lattice.to_lattice 𝔼

noncomputable instance : conditionally_complete_linear_order 𝔼 := 
{ Sup := 𝔼.Sup,
  Inf := 𝔼.Inf,
  le_cSup := λ T x hT1, le_cSup' T hT1 x,
  cSup_le := 
  begin
    intros T a hT ha,
    haveI : nonempty T := nonempty.to_subtype hT,
    exact cSup_le'' T a ha,
  end, 
  cInf_le := 
  begin
    intros T x hT hxT,
    simp only [𝔼.Inf],
    have hnnxT : - -x ∈ T, 
      simp, 
      exact hxT, 
    linarith[le_cSup' {x | -x ∈ T} (l35 hT) (-x) hnnxT],
  end,
  le_cInf := 
  begin
    intros T a hT ha,
    haveI : nonempty T := nonempty.to_subtype hT,
    have hnT : nonempty  {x | -x ∈ T},
      rcases nonempty_subtype.mp _inst with ⟨x,hx⟩,
    have hnnxT : - -x ∈ T, 
      simp, 
      exact hx,
    use [-x,hnnxT],  
    haveI : nonempty {x | -x ∈ T} := hnT,
    simp only [𝔼.Inf],
    linarith[cSup_le'' {x | -x ∈ T} (-a) (l34 a ha)],
  end,
  decidable_le := classical.dec_rel has_le.le,
  ..𝔼.linear_order,
  ..𝔼.lattice}
