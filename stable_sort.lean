section sort

theorem one_le_suc : ∀n, 1 ≤ nat.succ n :=
begin
    intros n,
    induction n,
        reflexivity,
    apply nat.less_than_or_equal.step,
    unfold has_le.le at ih_1,
    exact ih_1
end

def count_dec {α : Type} [decidable_eq α] : α → list α → ℕ
    | _ [] := 0
    | x (h :: t) := if x = h
                    then 1 + (count_dec x t)
                    else count_dec x t

def permutation_dec {α : Type} [decidable_eq α] (l₁ l₂ : list α) : Prop :=
    ∀x, count_dec x l₁ = count_dec x l₂

instance strict_order_pair_alpha_nat {α : Type} : strict_order (α × ℕ) :=
    { lt        := λl r, nat.lt l.snd r.snd,
      lt_irrefl := λpair, nat.lt_irrefl pair.snd,
      lt_trans  := λl m r, @nat.lt_trans l.snd m.snd r.snd}

def in_comp {α : Type} : α → list α → Prop
    | _ []       := false
    | x (h :: t) := x = h ∨ in_comp x t

local notation x ∈ l := in_comp x l

inductive no_dup {α : Type} : list α → Prop
    | no_dup_empty : no_dup []
    | no_dup_one   : ∀x, no_dup [x]
    | no_dup_more  : ∀x (l : list α),
                         no_dup l →
                         ¬(x ∈ l) →
                         no_dup (x :: l)

inductive sorted {α : Type} [decidable_linear_order α] : list α → Prop
    | sorted_empty : sorted []
    | sorted_one   : ∀x, sorted [x]
    | sorted_more  : ∀(x y : α) (t : list α),
                         x ≤ y → sorted (y :: t) → sorted (x :: y :: t)

inductive stable_sorted {α : Type} {β : Type}
                        [strict_order α] [decidable_linear_order β]
                        (key : α → β) :
    list α → Prop
    | stable_empty    : stable_sorted []
    | stable_one      : ∀x, stable_sorted [x]
    | stable_more_eq  : ∀(x y : α) (t : list α),
                            key x = key y →
                            x < y →
                            stable_sorted (y :: t) →
                            stable_sorted (x :: y :: t)
    | stable_more_neq : ∀(x y : α) (t : list α),
                            key x < key y →
                            stable_sorted (y :: t) →
                            stable_sorted (x :: y :: t)

open list
open sorted
open prod
open nat

lemma map_pres_nil {α β : Type} : ∀(l : list α) (f : α → β), 
    map f l = [] → l = [] :=
assume l f φ,
begin
    cases l,
        refl,
    dsimp at φ,
    cases φ
end

lemma map_pres_one {α β : Type} : ∀(l : list α) (x : β) (f : α → β),
    map f l = [x] → ∃y : α, l = [y] :=
assume l x f φ,
begin
    cases l,
        dsimp at φ, cases φ,
    cases a_1,
        existsi a, refl,
    cases φ
end

lemma map_pres_more {α β : Type} : ∀(l : list α) (t : list β) (x y : β) (f : α → β),
    map f l = x :: y :: t → ∃(a b : α) (c : list α), l = a :: b :: c :=
assume l t x y f φ,
begin
    cases l,
        dsimp at φ, cases φ,
    cases a_1,
        dsimp at φ, cases φ,
    dsimp at φ,
        existsi a,
        existsi a_2,
        existsi a_3,
        refl
end

lemma no_dup_tail {α : Type} : ∀h (t : list α),
    no_dup (h :: t) → no_dup (t) :=
assume h t φ,
begin
    cases φ,
        constructor,
    assumption
end

lemma not_in_means_neq {α : Type} : ∀(a b : α) (t : list α),
    ¬a ∈ b :: t → a ≠ b :=
assume a b t dec φ,
begin
    unfold not at φ,
    unfold in_comp at φ,
    rw φ at dec,
    unfold in_comp at dec,
    apply dec, left, refl
end

lemma no_dup_are_unequal {α : Type} : ∀(a b : α) (t : list α),
    no_dup (a :: b :: t) → a ≠ b :=
assume a b t φ,
begin
    cases φ,
    apply not_in_means_neq,
    exact a_2
end

lemma lt_le_neq {α : Type} [decidable_linear_order α] :
    ∀x y : α, x ≠ y → x ≤ y → x < y :=
assume x y φ ψ,
begin
    rw le_iff_lt_or_eq at ψ,
    cases ψ,
        exact a,
    contradiction
end

lemma map_over_nil {α β : Type} :
    ∀f : α → β,
    map f [] = [] := assume f, by refl

def π₁ {α : Type} : list (α × ℕ) → list α := map fst

theorem distinct_always_stable
    {α : Type}
    [x : decidable_linear_order α]
    [y : strict_order (α × ℕ)] :
    ∀(l : list (α × ℕ)),
    no_dup (π₁ l) → (
        @stable_sorted (α × ℕ) α y x fst l ↔
        @sorted α x (π₁ l)
    ) :=
assume l ω, 
begin
    unfold π₁ at *,
    split; intros φ,
    -- stable_sorted → sorted
    {
        induction φ with h h₁ h₂ t φ ψ ξ ih
                         h h₁ φ ψ ξ ih;
            -- trivial for empty list
            try {simp [map_over_nil]; constructor},
            {
                rw le_iff_lt_or_eq,
                right, assumption
            },            
            -- stable_sorted under equality
            -- follows from no_dup_shoter and ih
            {
                apply ih,
                dsimp at *,
                apply no_dup_tail,
                exact ω
            },
            -- trivial for singleton list
            {
                apply le_of_lt,
                exact ψ
            },
            -- stable_sorted under inequality
            -- follows from no_dup_shorter and ih
            {
                apply ih,
                dsimp at *,
                apply no_dup_tail,
                exact ω
            }
    },
    -- sorted → stable_sorted
    {
        -- consider a sorted fixed list l₁
        generalize2 (map fst l) l₁ ψ,
        rw ψ at φ,
        revert l,
        induction φ with h
                         h₁ h₂ t₁ φ ξ ih; intros,
        -- trivial for empty list
        {
            assert l_empty : l = [],
                apply map_pres_nil, exact ψ,
            rw l_empty, constructor
        },
        -- trivial for singleton list
        {
            assert l_single : ∃x, l = [x],
                apply map_pres_one, exact ψ,
            cases l_single with l₁ eq₁,
            rw eq₁,
            constructor
        },
        -- longer lists
        {
            assert l_more : ∃x₁ x₂ x₃, l = x₁ :: x₂ :: x₃,
                apply map_pres_more, exact ψ,
            cases l_more with x₁ eq₁,
            cases eq₁ with x₂ eq₂,
            cases eq₂ with x₃ eq₃,
            subst eq₃; dsimp at *,
            injection ψ with ψ₁ eq₄,
            injection eq₄ with ψ₂ eq₅,
            -- h₁ < h₂ ∨ h₁ = h₂
            rw le_iff_lt_or_eq at φ,
            cases φ with eq eq,
            -- h₁ < h₂
            -- follows from definition of stable_sortedness
            -- ih and no_dup_shorter
            {
                apply stable_sorted.stable_more_neq,
                    cc,
                apply ih; dsimp at *,
                    apply no_dup_tail,
                    exact ω,
                exact eq₄
            },
            -- h₁ = h₂
            -- problematic for stable_sort
            -- but we know that there are no duplicates
            -- the case is therefore contradictory
            {
                assert contra : x₁.fst ≠ x₂.fst,
                    apply no_dup_are_unequal,
                    exact ω,
                cc
            }
        }
    }
end

def iota_asc_from : ℕ → ℕ → list ℕ
    | m 0        := []
    | m (succ k) := m :: iota_asc_from (succ m) k

def iota_asc (n : ℕ) : list ℕ := iota_asc_from 0 n

lemma iota_asc_from_len : ∀m n,
    length (iota_asc_from m n) = n :=
assume m n,
begin
    revert m,
    induction n with n ih; intros,
        refl,
    unfold iota_asc_from length,
    rw add_one_eq_succ,
    apply congr_arg,
    apply ih
end

theorem iota_asc_len : ∀n,
    length (iota_asc n) = n := assume n, iota_asc_from_len 0 n

theorem no_dup_split {α : Type} : ∀h (t : list α),
    no_dup (h :: t) → no_dup t :=
assume h t φ,
begin
    cases φ, constructor, exact a
end

lemma iota_in_succ_succ : ∀m n k,
    n ∈ iota_asc_from m k →
    n ∈ iota_asc_from m (succ k) :=
assume m n k φ,
begin
    revert φ n m,
    induction k; intros m n φ,
    unfold iota_asc_from at *, cases φ, rename a a',
    unfold iota_asc_from,
    assert step : n ∈ m :: iota_asc_from (succ m) (succ a') →
                  n ∈ m :: succ m :: iota_asc_from (succ (succ m)) a',
        intros, unfold iota_asc_from at *, assumption,
    apply step, clear step,
    unfold in_comp, by_cases (m = n), left, rw h,
    right, apply ih_1,
    unfold iota_asc_from in_comp at φ,
    cases φ,
    rw eq_comm at a, contradiction,
    exact a
end

def add_key_from {α : Type} (l : list α) (n : ℕ) : list (α × ℕ) :=
    zip l (iota_asc_from n (length l))

def add_key {α : Type} (l : list α) : list (α × ℕ) :=
    add_key_from l 0

lemma pair_equal {α β : Type} : ∀p p' : α × β,
    p = p' ↔ p.fst = p'.fst ∧ p.snd = p'.snd :=
assume p p',
begin
    split; intros,
    split; cases a; refl,
    cases a, cases p, cases p',
    dsimp at *,
    cc
end

lemma add_key_from_immediate {α : Type} : ∀n h (t : list α),
    add_key_from (h :: t) n = (h, n) :: add_key_from t (succ n) :=
assume n h t, by refl

lemma add_key_from_nil {α : Type} :
    ∀n, add_key_from (@nil α) n = [] :=
assume n, by refl

lemma singleton_list_equal {α : Type} : ∀(x y : α),
    [x] = [y] ↔ x = y :=
assume x y,
begin
    split; intros,
    cases a, refl,
    cc
end

def insert_le {α : Type} [x : linear_weak_order α] [decidable_rel x.le] 
    : α → list α → list α
    | a []       := [a]
    | a (h :: t) := if a ≤ h
                    then a :: h :: t
                    else h :: insert_le a t

def insert_le_key {α : Type} [decidable_linear_order α]
    : (α × ℕ) → list (α × ℕ) → list (α × ℕ)
    | a []       := [a]
    | a (h :: t) := if a.fst ≤ h.fst
                    then a :: h :: t
                    else h :: insert_le_key a t

def insert_sort {α : Type} [x : decidable_linear_order α]
    (l : list α) : list (α × ℕ) :=
    foldr insert_le_key [] (add_key l)

def insert_sort_keyless {α : Type} [x : linear_weak_order α] [decidable_rel x.le] (l : list α) : (list α) :=
    foldr insert_le [] l

def π₁immediate {α : Type} : ∀(h₁ : α) h₂ (t : list (α × ℕ)),
    π₁ ((h₁, h₂) :: t) = h₁ :: π₁ t := assume h₁ h₂ t, by refl

lemma zip_l_nil {α β : Type} : ∀l : list α, zip l (@nil β) = (@nil (α × β)) :=
assume l,
begin
    cases l, refl, unfold zip zip_with, refl
end

lemma zip_nil_l {α β : Type} : ∀l : list α, zip (@nil β) l = (@nil (β × α)) :=
    assume l, by refl

lemma zip_immediate {α β : Type} : ∀h₁ h₂ (t₁ : list α) (t₂ : list β),
    zip (h₁ :: t₁) (h₂ :: t₂) = (h₁, h₂) :: zip t₁ t₂ :=
    assume h₁ h₂ t₁ t₂, by refl

lemma insert_into_nil {α : Type} [x : linear_weak_order α] [decidable_rel x.le] :
    ∀a, insert_le a (@nil α) = [a] := assume a, by refl

lemma insert_key_into_nil {α : Type} [x : decidable_linear_order α] :
    ∀a, insert_le_key a (@nil (α × ℕ)) = [a] := assume a, by refl

lemma sort_empty {α : Type} [x : decidable_linear_order α] :
    insert_sort (@nil α) = [] := by refl

lemma insert_into_empty {α : Type} [x : decidable_linear_order α] : ∀(h : α × ℕ),
    insert_le_key h nil = [h] := assume h, by refl

lemma one_add_eq_succ : ∀n : ℕ, 1 + n = succ n :=
    assume n, by rw add_comm

lemma zip_second_empty {α β : Type} : ∀(l : list α),
    zip_with mk l (@nil β) = nil := assume l, by cases l; refl

lemma add_key_cons {α : Type} : ∀h (t : list α),
    add_key (h :: t) = (h, 0) :: add_key_from t 1 := assume h t, rfl

lemma permutation_refl {α : Type} [decidable_eq α] : ∀(l : list α),
    permutation_dec l l := by simp [permutation_dec]

lemma count_dec_immediate {α : Type} [decidable_eq α] : ∀x (l : list α),
    count_dec x (x :: l) = succ (count_dec x l) :=
assume x l,
begin
    unfold count_dec,
    rw one_add_eq_succ,
    cc
end

lemma count_dec_not_immediate {α : Type} [decidable_eq α] : ∀x₁ x₂ (l : list α),
    x₁ ≠ x₂ → 
    count_dec x₁ (x₂ :: l) = count_dec x₁ l :=
assume x₁ x₂ l,
begin
    unfold count_dec,
    cc
end

lemma count_dec_eq_head {α : Type} [decidable_eq α] : ∀x h (t t' : list α),
    count_dec x (h :: t) = count_dec x (h :: t') ↔
    count_dec x t = count_dec x t' :=
assume x h t t',
begin
    split;
      unfold count_dec;
      by_cases (x = h) with ψ; simp [ψ]; intros φ,
        {repeat {rw one_add_eq_succ at φ},
         injection φ},
        {exact φ},
      {repeat {rw one_add_eq_succ}, apply congr_arg, exact φ},
      {exact φ}
end

lemma count_empty {α : Type} [decidable_eq α] : ∀x : α,
    count_dec x [] = 0 := assume x, by simp [count_dec]

lemma count_dec_app {α : Type} [decidable_eq α] : ∀x (l₁ l₂ : list α),
    count_dec x (l₁ ++ l₂) = count_dec x l₁ + count_dec x l₂ :=
assume x l l',
begin
    induction l with h t ih,
    {simp [nil_append, count_empty]},
    {unfold count_dec,
     by_cases (x = h) with φ; simp [φ],
       rw count_dec_immediate,
       rw one_add_eq_succ, 
       apply congr_arg,
       rw -φ,
       rw add_comm,
       exact ih,
     rw add_comm,
     rw -ih,
     unfold count_dec,
     cc
    }
end

lemma permutation_dec_eq_head {α : Type} [decidable_eq α] : ∀h (t t' : list α),
    permutation_dec t t' →
    permutation_dec (h :: t) (h :: t') :=
assume h t t' φ,
begin
    unfold permutation_dec,
    intros x,
    rw count_dec_eq_head,
    unfold permutation_dec at φ,
    apply φ
end

lemma list_len_mismatch {α : Type} : ∀h (t : list α),
    length (@nil α) ≠ length (h :: t) :=
assume h t, by contradiction

lemma permute_cons_diff {α : Type} [decidable_eq α] : ∀x y (t t' : list α),
    permutation_dec t (y :: t') →
    permutation_dec (x :: t) (y :: x :: t') :=
assume x y t t' φ,
begin
    unfold permutation_dec count_dec, intros h,
    by_cases (h = x) with ψ; simp [ψ],
        by_cases (x = y) with ξ; simp [ξ],
            repeat {rw one_add_eq_succ},
            apply congr_arg,
            unfold permutation_dec at φ,
            assert ih_fix :
                count_dec y t = count_dec y (y :: t'),
                begin apply φ end,
            rw ih_fix,
            simp [count_dec_immediate],
        repeat {rw one_add_eq_succ},
        apply congr_arg,
        unfold permutation_dec at φ,
        assert ih_fix :
            count_dec x t = count_dec x (y :: t'),
        begin apply φ end,
        rw ih_fix,
        rw count_dec_not_immediate, cc,
        by_cases (h = y) with ψ; simp [ψ],
            unfold permutation_dec at φ,
            assert ih_fix :
                count_dec y t = count_dec y (y :: t'),
                begin apply φ end,
            rw ih_fix,
            rw count_dec_immediate,
            rw one_add_eq_succ,
        unfold permutation_dec at φ,
        assert ih_fix :
            count_dec h t = count_dec h (y :: t'),
            begin apply φ end,
        rw ih_fix,
        rw count_dec_not_immediate,
        cc
end

lemma insert_permutes {α : Type} [x : decidable_linear_order α] : ∀h (t : list (α × ℕ)),
    permutation_dec (insert_le_key h t) (h :: t) :=
assume h t,
begin
    induction t with h' t' ih,
    {simp [insert_into_empty, permutation_refl]},
    {unfold insert_le_key,
     by_cases (h.fst ≤ h'.fst) with h;
     unfold strong_order_pair.le linear_strong_order_pair.le decidable_linear_order.le;
     simp [h],
         apply permutation_refl,
         apply permute_cons_diff,
         exact ih
    }
end

lemma count_over_projection {α : Type} [x : decidable_linear_order α] :
    ∀x xₖ (l : list (α × ℕ)),
    count_dec x (π₁ (insert_le_key (x, xₖ) l)) = succ (count_dec x (π₁ l)) :=
assume x xₖ l,
begin
    induction l,
    {rw insert_into_empty,
     unfold π₁,
     dsimp,
     rw count_dec_immediate
    },
    {unfold insert_le_key,
     dsimp,
     by_cases (x ≤ a.fst) with φ;
     unfold strong_order_pair.le linear_strong_order_pair.le decidable_linear_order.le; simp [φ],
       unfold π₁, dsimp,
       rw count_dec_immediate,
     unfold π₁ at *, dsimp at *,
     rename x_1 x₁,
     assert neq_if_nleq : x₁ ≠ a.fst,
       dsimp, unfold not, intros contra,
       assert if_nleq : x₁ ≤ a.fst,
         apply le_of_eq, exact contra,
       contradiction,
     repeat {rw count_dec_not_immediate},
     exact ih_1, cc, cc
    }
end

lemma count_over_projection_neq
    {α : Type}
    [x : decidable_linear_order α] :
    ∀x y xₖ (l : list (α × ℕ)),
        x ≠ y → 
        count_dec x (π₁ (insert_le_key (y, xₖ) l)) = count_dec x (π₁ l) :=
assume x y xₖ l,
begin
    induction l; intros φ,
    {
        rw insert_into_empty,
        unfold π₁,
        dsimp,
        rw count_dec_not_immediate,
        exact φ
    },
    {
        unfold insert_le_key,
        dsimp,
        by_cases (y ≤ a.fst) with ψ;
            unfold strong_order_pair.le linear_strong_order_pair.le decidable_linear_order.le; simp [ψ],
            rw π₁immediate,
            rw count_dec_not_immediate, exact φ,
        unfold π₁ at *, dsimp at *,
        rename x_1 x₁,
        note ihₕ := ih_1 φ,
        unfold count_dec,
        by_cases (x₁ = a.fst) with ξ;
        unfold has_le.le weak_order.le; simp [ξ],
        repeat {rw one_add_eq_succ},
            apply congr_arg,
            cc,
        cc
    }
end

lemma projection_over_pairs
    {α : Type} :
    ∀(l₁ : list α)(l₂ : list ℕ),
        length l₁ = length l₂ →
        ∀l, (length l₁ = length l) →
            π₁ (zip l₁ l₂) = π₁ (zip l₁ l) :=
assume l₁,
begin
    induction l₁ with h t ih; intros l₂ φ l,
        repeat {rw zip_nil_l}, intros, refl,
    intros ψ,
    cases l₂ with a₁; dsimp at φ,
        cases φ,
    dsimp at φ, repeat {rw add_one_eq_succ at φ},
    injection φ with eq_len,
    cases l with h₁ t₁,
        cases ψ,
    dsimp at ψ, repeat {rw add_one_eq_succ at ψ},
    injection ψ with eq_lenψ,
    note ih_fix := ih a eq_len t₁ eq_lenψ,
    repeat {rw zip_immediate},
    repeat {rw π₁immediate},
    apply congr_arg,
    exact ih_fix
end

lemma insert_second_irrelevant
    {α : Type}
    [x : decidable_linear_order α] :
    ∀a b c (l : list (α × ℕ)),
        π₁ (insert_le_key (a, b) l) = π₁ (insert_le_key (a, c) l) :=
assume a b c l,
begin
    induction l with h t ih,
        repeat {rw insert_key_into_nil}, refl,
    unfold insert_le_key, dsimp,
    by_cases (a ≤ h.fst) with ψ;
    unfold strong_order_pair.le linear_strong_order_pair.le decidable_linear_order.le;
    simp [ψ],
        repeat {rw π₁immediate},
    cases h,
    repeat {rw π₁immediate},
    apply congr_arg,
    exact ih
end

lemma insert_le_x_right_neutral
    {α : Type}
    [decidable_linear_order α] :
    ∀x (l₁ l₂ : list (α × ℕ)),
        π₁ l₁ = π₁ l₂ → 
        π₁ (insert_le_key x l₁) = π₁ (insert_le_key x l₂) :=
assume x l₁,
begin
    induction l₁ with h t ih; intros l₂ φ; cases l₂ with h₂ t₂,
    -- trivial for empty lists
    {
        refl
    },
    -- contradictory for lists of unequal lengths
    {
        contradiction
    },
    {
        contradiction
    },
    {
        unfold insert_le_key at *,
        by_cases (x.fst ≤ h.fst) with ψ;
            by_cases (x.fst ≤ h₂.fst) with ξ;
                simp [ψ, ξ]; unfold π₁ at *; dsimp at *;
                    injection φ with eq₁ eq₂;
                try {try {apply congr_arg}; cc},
        rw eq₁, apply congr_arg, apply ih, exact eq₂
    }
end

lemma projection_over_foldr
    {α : Type}
    [x : decidable_linear_order α] :
    ∀(l : list α) (l₁ l₂ : list ℕ),
        length l₁ = length l₂ → 
        π₁ (foldr insert_le_key nil (zip l l₁)) =
        π₁ (foldr insert_le_key nil (zip l l₂)) :=
assume l,
begin
    induction l with h t ih; intros l₁ l₂ φ,
        repeat {rw zip_nil_l},
    cases l₁ with h₁ t₁; cases l₂ with h₂ t₂,
        rw zip_l_nil, 
        contradiction,
        contradiction,
    repeat {rw zip_immediate},
    dsimp,
    dsimp at φ, repeat {rw add_one_eq_succ at φ}, injection φ with H,
    note ih₁ := ih t₁ t₂ H,
    rw (@insert_second_irrelevant _ _ h h₂ h₁ _),
    apply insert_le_x_right_neutral,
    exact ih₁   
end

lemma sort_permutes
    {α : Type}
    [decidable_linear_order α] :
    ∀l₁ (l₂ : list (α × ℕ)), 
        l₂ = insert_sort l₁ → permutation_dec (π₁ l₂) l₁ :=
assume l₁ l₂ φ,
begin
    revert l₂ φ,
    induction l₁ with h t ih; intros,
    -- l₁ = ε
    {
        assert l₂_nil : l₂ = [],
            rw φ, apply sort_empty,
            rw l₂_nil,
        unfold π₁ permutation_dec,
        intros, refl
    },
    -- l₁ = h :: t
    {
        subst φ,
        unfold insert_sort,
        rw add_key_cons,
        unfold foldr,
        assert ih₁ : permutation_dec (π₁ (insert_sort t)) t,
            apply ih, refl,
        unfold permutation_dec at *,
        intros hₑ,
        unfold count_dec,
        -- assuming hₑ = h
        -- follows from ih count_over_projection
        -- projection_over_foldr iota_asc_from_len
        by_cases (hₑ = h) with ψ; simp [ψ],
        {
            rw count_over_projection,
            rw one_add_eq_succ,
            apply congr_arg,
            note ihₕ := ih₁ h,
            unfold insert_sort at ihₕ,
            unfold add_key_from add_key at *,
            rw (@projection_over_foldr _ _ t _ (iota_asc_from 0 (length t))),
                exact ihₕ,
            simp [iota_asc_from_len]
        },
        -- assuming hₑ ≠ h
        -- follows from ih count_over_projection_neq
        -- projection_over_foldr iota_asc_from_len
        {
            note ihₑ := ih₁ hₑ,
            rw -ihₑ,
            unfold insert_sort add_key,
            rw count_over_projection_neq,
            unfold insert_sort add_key add_key_from at *,
            rw (@projection_over_foldr _ _ t _ (iota_asc_from 0 (length t))),
            simp [iota_asc_from_len],
            cc
        }
    }

end

inductive strictly_increasing : list ℕ → Prop
    | si_empty : strictly_increasing []
    | si_one   : ∀x, strictly_increasing [x]
    | si_more  : ∀h₁ h₂ (t : list ℕ),
                 h₁ < h₂ →
                 strictly_increasing (h₂ :: t) →
                 strictly_increasing (h₁ :: h₂ :: t)

lemma iota_excl : ∀m n l,
    iota_asc_from m n = l →
    ∀x, x ∈ l → m ≤ x:=
assume m n,
begin
    revert m,
    induction n with k ih; intros m l φ x ψ,
        unfold iota_asc_from at φ, subst φ, cases ψ,
    cases l with h t,
        cases ψ,
    by_cases (x = h) with H,
        unfold iota_asc_from at φ,
        injection φ with ξ ρ,
        subst H, subst ξ,
    unfold iota_asc_from at φ,
    injection φ with h₁ h₂,
    unfold in_comp at ψ,
    cases ψ with head tail,
        contradiction,
    note ih₁ := ih (succ m) t h₂ x tail,
    apply le_of_succ_le,
    exact ih₁
end

theorem iota_from_strictly : ∀m n l,
    l = iota_asc_from m n → 
    strictly_increasing l :=
assume m n l φ,
begin
    subst φ,
    revert m,
    induction n with k ih; intros m,
        constructor,
    unfold iota_asc_from,
    generalize2 (iota_asc_from (succ m) k) G H,
    cases G,
        constructor,
    constructor,
    apply lt_of_succ_le,
        apply iota_excl,
        exact H,
        unfold in_comp,
        left,
        refl,
    rw -H,
    apply ih    
end

lemma le_succ_succ_of : ∀m n, succ m ≤ succ n → m ≤ n :=
assume m n φ, @pred_le_pred (succ m) (succ n) φ

lemma stable_sorted_over_zip {α : Type} [x : decidable_linear_order α] [decidable_rel x.le] [decidable_eq α] :
    ∀h₁ h₂ (t₁ : list α) (t₂ : list ℕ),
    t₁ = [] →
    length t₁ = length t₂ →
    stable_sorted fst (foldr insert_le_key nil (zip t₁ t₂)) →
    stable_sorted fst (foldr insert_le_key nil (zip (h₁ :: t₁) (h₂ :: t₂))) :=
assume h₁ h₂ t₁ t₂ φ ψ ξ,
begin
    subst φ, cases t₂, rw zip_immediate, rw zip_nil_l,
    unfold foldr insert_le_key, constructor,
    contradiction
end

lemma strictly_increasing_over_head : ∀h t,
    strictly_increasing (h :: t) →
    strictly_increasing t :=
assume h t φ,
begin
    cases φ,
        constructor,
    exact a_1
end

lemma insert_inc_len {α : Type} [x : decidable_linear_order α] :
    ∀a (l : list (α × ℕ)),
    length (insert_le_key a l) = succ (length l) :=
assume a l,
begin
    induction l, dsimp, rw insert_key_into_nil,
    refl,
    unfold insert_le_key,
    by_cases (a.fst ≤ a_1.fst) with H;
    unfold strong_order_pair.le linear_strong_order_pair.le decidable_linear_order.le;
    simp [H],
    rw one_add_eq_succ,
    rw one_add_eq_succ,
    apply congr_arg, rw ih_1,
    rw one_add_eq_succ
end

lemma insert_twice_len {α : Type} [x : decidable_linear_order α] :
    ∀a b (l : list (α × ℕ)), 
        length (insert_le_key a (insert_le_key b l)) ≥ 2 :=
assume a b l,
begin
    rw insert_inc_len, rw insert_inc_len,
    dsimp, induction l, refl,
    unfold length, rw add_one_eq_succ, apply le_succ_of_le,
    exact ih_1
end

lemma len_congr {α : Type} :
    ∀l₁ l₂ : list α,
    l₁ = l₂ → length l₁ = length l₂ :=
assume l₁ l₂ φ,
begin
    induction l₁, subst φ, 
    rw φ
end

lemma fold_zip_singular {α : Type} [x : decidable_linear_order α] :
    ∀(l₁ : list α) l₂ x,
    length l₁ = length l₂ →
    foldr insert_le_key nil (zip l₁ l₂) = [x] →
    l₁ = [x.fst] ∧ l₂ = [x.snd] :=
assume l₁ l₂ x ψ φ,
begin
    split,
        cases l₁; cases l₂, rw zip_nil_l at φ, unfold foldr at φ, contradiction,
            rw zip_nil_l at φ, unfold foldr at φ, contradiction,
        rw zip_l_nil at φ, unfold foldr at φ, contradiction,
        rw zip_immediate at φ, cases a_1, rw zip_nil_l at φ,
        unfold foldr at φ, rw insert_key_into_nil at φ,
        injection φ with G H, subst G,
        cases a_3, rw zip_l_nil at φ,
        unfold length at ψ, rw zero_add at ψ,
        repeat {rw add_one_eq_succ at ψ},
        cases ψ,
        rw zip_immediate at φ,
        unfold foldr at φ,
        unfold insert_le_key at φ,
        note len := len_congr _ _ φ,
        dsimp at len,
        rw zero_add at len,
        rw insert_inc_len at len,
        rw insert_inc_len at len,
        cases len,
        cases l₂,
            rw zip_l_nil at φ, dsimp at φ, contradiction,
        cases l₁,
            dsimp at ψ, rw add_one_eq_succ at ψ, contradiction,
        cases a_1; cases a_3,
            rw zip_immediate at φ, rw zip_nil_l at φ,
            dsimp at φ, rw insert_key_into_nil at φ,
            injection φ with A B,
            subst A,
        dsimp at ψ, rw add_one_eq_succ at ψ,
        rw zero_add at ψ, cases ψ,
        dsimp at ψ, rw add_one_eq_succ at ψ,
        rw add_one_eq_succ at ψ,
        rw add_one_eq_succ at ψ,
        cases ψ,
        repeat {rw zip_immediate at φ},
        dsimp at φ,
        note len := len_congr _ _ φ,
        repeat {rw insert_inc_len at len},
        dsimp at len,
        rw zero_add at len,
        cases len
end

lemma zero_le_true_iff : ∀n, nat.less_than_or_equal 0 n ↔ true :=
assume n,
begin
    split; intros,
        cc,
    induction n,
    unfold linear_weak_order.le,
        unfold nat.le,
        constructor,
    unfold linear_weak_order.le nat.le,
    constructor,
    exact ih_1     
end

lemma strictly_into_head : ∀h h₁ t,
    h < h₁ →
    strictly_increasing (h₁ :: t) →
    strictly_increasing (h :: h₁ :: t) :=
assume h h₁ t φ ψ,
begin
    generalize2 (h₁ :: t) l ρ,
        rw ρ at ψ,
    revert h h₁ t φ,
    induction ψ; intros,
        constructor,
        cases ρ, constructor, exact φ,
        constructor,
    constructor,
    cases ρ, exact φ,
    note ih₁ := ih_1 h₁ h₂ t a,
    apply ih₁, refl
end

lemma   strictly_over_skip : ∀h h₁ t,
    strictly_increasing (h :: h₁ :: t) →
    strictly_increasing (h :: t) :=
assume h h₁ t φ,
begin
    cases φ,
    cases a_1,
        constructor,
    apply strictly_into_head,
    apply (@lt_trans _ _ _ h₁); try {assumption},
    exact a_3
end

lemma strictly_split : ∀h t,
    strictly_increasing (h :: t) →
    (∀x, x ∈ t → h < x) :=
assume h t φ,
begin
    induction t with h₁ t₁ ih; intros,
        cases a,
    unfold in_comp at a,
        cases a,
        rw -a_1 at φ,
        cases φ, exact a,
    apply ih,
    note ρ := strictly_increasing (h :: t₁),
         apply strictly_over_skip, exact φ,
    exact a_1
end

lemma project_second {α : Type} :
    ∀x y (l : list α) (l₁ : list ℕ),
    length l = length l₁ →
    (x, y) ∈ zip l l₁ →
    y ∈ l₁ :=
assume x y l l₁ φ ψ,
begin
    revert ψ,
    generalize2 (zip l l₁) l' ρ,
    intros,
    revert x y l l₁ φ,
    induction l'; intros,
        cases ψ,
    unfold in_comp at ψ,
    cases ψ,
        cases a,
        cases a_2,
        cases l; cases l₁,
            rw zip_nil_l at ρ,
            cases ρ,
            rw zip_nil_l at ρ,
            cases ρ,
            unfold length at φ,
            rw add_one_eq_succ at φ,
            cases φ,
            rw zip_immediate at ρ,
            injection ρ with A B,
            cases A,
            unfold in_comp, left, refl,
        cases l; cases l₁,
            rw zip_nil_l at ρ,
            cases ρ,
            rw zip_nil_l at ρ,
            cases ρ,
            rw zip_l_nil at ρ,
            cases ρ,
            rw zip_immediate at ρ,
            injection ρ,
        unfold length at φ,
        repeat {rw add_one_eq_succ at φ},
        injection φ with ω,
        note ih := ih_1 x y a_4 a_6 ω h a_2,
        unfold in_comp,
        right,
        exact ih
end

lemma insert_always_in {α : Type} [decidable_linear_order α] :
    ∀x (l : list (α × ℕ)),
    x ∈ insert_le_key x l :=
assume x l,
begin
    induction l,
    rw insert_key_into_nil,
    unfold in_comp, left, refl,
    unfold insert_le_key,
    by_cases (x.fst ≤ a.fst) with h; simp [h],
    unfold in_comp, left, refl,
    unfold in_comp, right, exact ih_1
end

lemma insert_pres_in {α : Type} [decidable_linear_order α] :
    ∀x y (l : list (α × ℕ)),
    y ∈ l → 
    y ∈ insert_le_key x l :=
assume x y l φ,
begin
    induction l,
        cases φ,
    unfold in_comp at φ; cases φ,
    rw a_2,
        unfold insert_le_key,
        by_cases (x.fst ≤ a.fst) with h; simp [h],
            unfold in_comp,
                right, left, refl,
            unfold in_comp,
                left, refl,
            unfold insert_le_key,
            by_cases (x.fst ≤ a.fst) with g; simp [g],
                unfold in_comp,
                    right, right, exact a_2,
                unfold in_comp,
                    right, apply ih_1, exact a_2
end

lemma list_len_shorter {α β : Type} :
    ∀h h₁ (t : list α) (t₁ : list β),
    length (h :: t) = length (h₁ :: t₁) →
    length t = length t₁ :=
assume h h₁ t t₁ φ,
begin
    unfold length at φ,
    repeat {rw add_one_eq_succ at φ},
    injection φ
end

lemma in_immediate {α : Type} : ∀h (t : list α), h ∈ h :: t :=
assume h t, by unfold in_comp; left; refl

lemma leq_to_orq {α : Type} [decidable_linear_order α] :
    ∀a b : α, a ≠ b → ¬(a ≤ b) → b < a :=
assume a b ψ φ,
begin
    cases (lt_trichotomy a b),
        rw le_iff_lt_or_eq at φ,
    by_cases (a < b) with h,
        cc, cc,
    cases a_1,
        cc, assumption
end

def π₂ {α : Type} (l : list (α × ℕ)) : list ℕ := map snd l

lemma iota_split :
    ∀h t m n,
    1 ≤ n →
    h :: t = iota_asc_from m n → 
    h = m ∧ t = iota_asc_from (succ m) (pred n) :=
assume h t m n φ ψ,
begin
    split,
    -- h = m
    {cases n, cases φ, unfold iota_asc_from at ψ, injection ψ},
    -- t = iota_sac_from (succ m) (pred n)
    {
        cases n, cases φ,
        unfold iota_asc_from at ψ,
        injection ψ    
    }
end

lemma in_π₂_immediate {α : Type} :
    ∀(h : α × ℕ) (t : list (α × ℕ)),
    h.snd ∈ π₂ (h :: t) :=
assume h t,
begin
    unfold π₂, dsimp, apply in_immediate
end

lemma in_extended {α : Type} :
    ∀x y (l : list (α × ℕ)),
    x ∈ π₂ l →
    x ∈ π₂ (y :: l) :=
assume x y l φ,
begin
    unfold π₂, dsimp, unfold in_comp, right, assumption
end

lemma le_contra {α : Type} [decidable_linear_order α] :
    ∀x y : α,
        x = y →
        ¬x ≤ y →
        false :=
assume x y φ ψ,
begin
    rw φ at ψ,
    assert contra : y ≤ y, apply le_refl,
    contradiction
end

lemma insert_pres_sorted {α : Type} [decidable_linear_order α] :
    ∀l (e : α × ℕ) elem key,
    e = (elem, key) →
    (∀x, x ∈ π₂ l → key < x) →
    stable_sorted fst l →
    stable_sorted fst (insert_le_key e l) :=
assume l e elem key φ ψ ξ,
begin
    subst φ,
    induction l with h t ih,
    {
        rw insert_key_into_nil,
        constructor
    },
    {
        dsimp,
        unfold insert_le_key, dsimp,
        by_cases (elem = h.fst) with H;
            by_cases (elem ≤ h.fst) with H₁;
                simp [H₁],
        {
            apply stable_sorted.stable_more_eq;
                try{assumption},
            apply ψ,
            apply in_π₂_immediate
        },
        {
            note contra := le_contra elem h.fst, cc
        },
        {
            apply stable_sorted.stable_more_neq; dsimp,
            apply lt_le_neq; assumption,
            assumption
        },
        {
            cases ξ; by_cases (h.fst = elem) with G; try{cc},
            {
                apply stable_sorted.stable_more_neq; dsimp;
                    try{cc},
                apply leq_to_orq; assumption,
                constructor
            },
            {
                unfold insert_le_key; dsimp, 
                by_cases (elem ≤ y.fst) with J,
                {
                    cc
                },
                {
                    simp [J],
                    apply stable_sorted.stable_more_eq,
                        try{cc},
                    assumption,
                    assert folded : y :: insert_le_key (elem, key) t_2 =
                                    insert_le_key (elem, key) (y :: t_2),
                        unfold insert_le_key, dsimp, simp [J],
                    rw folded,
                    apply ih,
                        intros x eqₓ,
                        apply ψ,
                    apply in_extended, assumption,
                    assumption,
                }
            },
            {
                unfold insert_le_key; dsimp,
                by_cases (elem ≤ y.fst) with J; simp [J],
                {
                    apply stable_sorted.stable_more_neq; dsimp;
                        try{cc},
                    apply leq_to_orq; cc,
                    by_cases (elem = y.fst) with K,
                    {
                        apply stable_sorted.stable_more_eq; dsimp;
                            try{cc},
                        apply ψ,
                        apply in_extended,
                        apply in_π₂_immediate
                    },
                    {
                        apply stable_sorted.stable_more_neq; dsimp;
                            try{cc},
                        apply lt_le_neq; cc
                    }
                },
                {
                    apply stable_sorted.stable_more_neq; dsimp;
                        try{cc},
                    assert folded : y :: insert_le_key (elem, key) t_2 =
                                    insert_le_key (elem, key) (y :: t_2),
                        unfold insert_le_key, dsimp, simp [J],
                    rw folded,
                    apply ih,
                        intros x eqₓ,
                        apply ψ,
                        apply in_extended, assumption,
                    assumption
                }
            }
        }
    }
end

lemma over_second_split {α : Type} [decidable_linear_order α] :
    ∀x elem idx (l : list (α × ℕ)),
    x ∈ π₂ (insert_le_key (elem, idx) l) →
    x = idx ∨ x ∈ π₂ l :=
assume x elem key l φ,
begin
    induction l with h t ih,
        {rw insert_key_into_nil at φ,
         unfold π₂ at φ, dsimp at φ, unfold in_comp at φ,
         cases φ, left, assumption, contradiction},
        {
            unfold insert_le_key at φ, dsimp at φ,
            by_cases (elem ≤ h.fst) with H; simp [H] at φ,
                unfold π₂ at φ, dsimp at φ,
                unfold in_comp at φ, cases φ, left, assumption,
                cases a, right, unfold π₂, dsimp,
                unfold in_comp, left, assumption, right,
                unfold in_comp, unfold π₂, dsimp,
                unfold in_comp, right, assumption,
            unfold π₂, dsimp, unfold in_comp,
            unfold π₂ at φ, dsimp at φ,
            unfold in_comp at φ, cases φ,
            right, left, exact a,
            assert or_split : ∀x y z, x ∨ z → x ∨ y ∨ z,
                intros, cases a_1, left, assumption, 
                right, right, assumption,
            apply or_split, apply ih, assumption
        }
end

lemma over_second_projection {α : Type} [decidable_linear_order α] :
    ∀x (l₁ : list α) (l₂ : list ℕ),
    length l₁ = length l₂ →
    x ∈ π₂ (foldr insert_le_key nil (zip l₁ l₂)) →
    x ∈ l₂ :=
assume x l₁ l₂ ψ φ,
begin
    revert l₂,
    induction l₁ with h t ih; intros,
        rw zip_nil_l at φ,
        unfold foldr π₂ at φ,
        dsimp at φ,
        unfold in_comp at φ,
        contradiction,
    cases l₂ with h₂ t₂,
        unfold length at ψ,
        rw add_one_eq_succ at ψ,
        cases ψ,
    rw zip_immediate at φ,
    unfold foldr at φ,
    assert split : x = h₂ ∨ 
                   x ∈ π₂ (foldr insert_le_key nil (zip t t₂)),
        apply over_second_split, assumption,
    cases split,
        unfold in_comp, left, assumption,
    unfold in_comp, right, apply ih, apply list_len_shorter, assumption,
    assumption
end

lemma sort_sorts_stabily_aux {α : Type} [decidable_linear_order α] :
    ∀(l : list (α × ℕ)) (l₁ : list α) (l₂ : list ℕ) m n,
        length l₁ = length l₂ →
        l₂ = iota_asc_from m n →
        l = foldr insert_le_key [] (zip l₁ l₂) →
        stable_sorted fst l :=
assume l l₁ l₂ m n φ ψ ξ,
begin
    revert l l₂ m n,
    induction l₁ with h t ih; intros; cases l₂ with h₂ t₂,
        -- l₁ = ε
        {rw zip_l_nil at ξ, unfold foldr at ξ, rw ξ, constructor},
        -- contradiction by list length mismatch
        {note contra := list_len_mismatch h₂ t₂, contradiction},
        {note contra := list_len_mismatch h t, contradiction},
        -- l₁ l₂ of h :: t
        {
            rw ξ,
            rw zip_immediate,
            unfold foldr,
            assert split_iota_asc :
                    h₂ = m ∧ t₂ = iota_asc_from (succ m) (pred n),
                    apply iota_split,
                    -- in h :: t, there is at least one
                    cases n, unfold iota_asc_from at ψ, cases ψ,
                    apply one_le_suc,
                    exact ψ,
            cases split_iota_asc with eq₁ eq₂,
            assert iota_always_strictly : strictly_increasing (h₂ :: t₂),
                apply iota_from_strictly, exact ψ,
            assert tails_strictly_inc : strictly_increasing t₂,
                apply strictly_increasing_over_head,
                exact iota_always_strictly,
            note tails_eq_len := list_len_shorter _ _ _ _ φ,
            apply insert_pres_sorted,
                -- insert (h₁, h₂) 
                refl,
                -- stability preserving condition
                intros x eqₓ,
                assert eq₁ : x ∈ t₂,
                    apply over_second_projection,
                    apply list_len_shorter,
                    assumption,
                    assumption,
                apply strictly_split, assumption,
                assumption,
            -- follows from ih for a strictly shorter list
            apply ih,
                exact tails_eq_len,
                exact eq₂,
                refl
        }
end

lemma sort_sorts_stabily {α : Type} [x : decidable_linear_order α] :
    ∀(l₁ : list α)(l₂ : list (α × ℕ)), 
        l₂ = insert_sort l₁ → stable_sorted fst l₂ :=
assume l₁ l₂ φ,
begin
    unfold insert_sort add_key add_key_from at φ,
    apply (@sort_sorts_stabily_aux _ _ _ l₁ (iota_asc_from 0 (length l₁))),
        -- length of zipped lists coincide
        {
            assert lens_eq : length (iota_asc_from 0 (length l₁)) = length l₁,
                apply iota_asc_len,
                symmetry,
                exact lens_eq
        },
        -- iota asc from is irrelevant as long as it is strictly increasing
        {
            refl
        },
        -- list fits into the auxiliary lemma
        {
            exact φ
        }
end

theorem sort_correct_and_stable {α : Type} [decidable_linear_order α] :
    ∀(l₁ : list α) (l₂ : list (α × ℕ)),
        l₂ = insert_sort l₁ → 
        stable_sorted fst l₂ ∧
        permutation_dec (π₁ l₂) l₁ :=
assume l₁ l₂ φ,
begin
    split,
    {apply sort_sorts_stabily, exact φ},
    {apply sort_permutes, exact φ}
end

def sort {α : Type} [decidable_linear_order α] :
    list α → list α := π₁ ∘ insert_sort

theorem insert_sort_well_behaved {α : Type} [decidable_linear_order α] :
    ∀l : list α, π₁ (insert_sort l) = sort l :=
assume l, by refl

end sort













