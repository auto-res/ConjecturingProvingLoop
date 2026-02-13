

theorem P1_sUnion_empty {X : Type*} [TopologicalSpace X] : P1 (⋃₀ (∅ : Set (Set X))) := by
  simpa [Set.sUnion_empty] using (P1_empty : P1 (∅ : Set X))

theorem P2_union_distrib {X : Type*} [TopologicalSpace X] {A B C : Set X} : P2 (A ∪ (B ∩ C)) ↔ P2 ((A ∪ B) ∩ (A ∪ C)) := by
  classical
  -- First, record the set-theoretic identity we need.
  have h_eq : (A ∪ (B ∩ C) : Set X) = (A ∪ B) ∩ (A ∪ C) := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA =>
          exact ⟨Or.inl hA, Or.inl hA⟩
      | inr hBC =>
          exact ⟨Or.inr hBC.1, Or.inr hBC.2⟩
    · intro hx
      rcases hx with ⟨hAB, hAC⟩
      cases hAB with
      | inl hA =>
          exact Or.inl hA
      | inr hB =>
          cases hAC with
          | inl hA =>
              exact Or.inl hA
          | inr hC =>
              exact Or.inr ⟨hB, hC⟩
  -- The desired equivalence now follows by rewriting with `h_eq`.
  constructor
  · intro hP2
    simpa [h_eq] using hP2
  · intro hP2
    simpa [h_eq] using hP2

theorem P3_prod_distrib {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (Set.image (fun xyz : X × Y × Z => (xyz.1, (xyz.2).1, (xyz.2).2)) (A ×ˢ B ×ˢ C)) := by
  intro xyz hx
  rcases hx with ⟨xyz0, hmem, rfl⟩
  rcases xyz0 with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  -- Extract component-wise membership
  have hxA : x ∈ A := hmem.1
  have hyz : (y, z) ∈ B ×ˢ C := hmem.2
  have hyB : y ∈ B := hyz.1
  have hzC : z ∈ C := hyz.2
  -- Apply the P3 hypotheses
  have hx_int : x ∈ interior (closure A) := hA hxA
  have hy_int : y ∈ interior (closure B) := hB hyB
  have hz_int : z ∈ interior (closure C) := hC hzC
  -- Build interior membership for the (B ×ˢ C) part
  have hBC_int : (y, z) ∈ interior (closure (B ×ˢ C)) := by
    have : (y, z) ∈ interior (closure B) ×ˢ interior (closure C) := by
      exact ⟨hy_int, hz_int⟩
    simpa [closure_prod_eq, interior_prod_eq] using this
  -- Combine everything for the triple product
  have hprod :
      (x, (y, z)) ∈
        interior (closure A) ×ˢ interior (closure (B ×ˢ C)) := by
    exact ⟨hx_int, hBC_int⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P1_sigma {α : Type*} {β : α → Type*} [∀ a, TopologicalSpace (β a)] (s : Set α) (t : ∀ a, Set (β a)) (h : ∀ a, P1 (t a)) : P1 {p : Sigma β | p.1 ∈ s ∧ p.2 ∈ t p.1} := by
  classical
  -- Put the target set in a local name.
  let S : Set (Sigma β) := {q | q.1 ∈ s ∧ q.2 ∈ t q.1}
  intro p hp
  -- Decompose the Σ–point.
  rcases p with ⟨a, b⟩
  -- Separate the component hypotheses.
  have ha : a ∈ s := hp.1
  have hb : b ∈ t a := hp.2
  -- Use the fibrewise `P1` assumption.
  have hb_cl : b ∈ closure (interior (t a)) := (h a) hb
  -- We prove that `(a , b)` lies in the closure of the interior of `S`.
  have h_cl : (⟨a, b⟩ : Sigma β) ∈ closure (interior S) := by
    -- Neighbourhood characterisation of `closure`.
    apply (mem_closure_iff).2
    intro U hU_open hU_mem
    -- Slice `U` along the fibre over `a`.
    let V : Set (β a) := {b' | (⟨a, b'⟩ : Sigma β) ∈ U}
    have hV_open : IsOpen V := by
      -- The map `b' ↦ (a , b')` is continuous.
      have hcont : Continuous fun b' : β a => (⟨a, b'⟩ : Sigma β) := by
        continuity
      simpa [V] using hU_open.preimage hcont
    have hbV : b ∈ V := by
      simpa [V] using hU_mem
    -- Because `b ∈ closure (interior (t a))`, `V` meets `interior (t a)`.
    have h_non : (V ∩ interior (t a)).Nonempty := by
      have := (mem_closure_iff).1 hb_cl V hV_open hbV
      simpa [Set.inter_comm] using this
    rcases h_non with ⟨b', hb'V, hb'int⟩
    --------------------------------------------------------------------
    -- Construct an auxiliary open set contained in `S`.
    --------------------------------------------------------------------
    -- Define a fibrewise set choosing `interior (t a')` when `a' ∈ s`.
    let F : ∀ a', Set (β a') := fun a' =>
      if h' : a' ∈ s then interior (t a') else ∅
    have hF_open : ∀ a', IsOpen (F a') := by
      intro a'
      by_cases h' : a' ∈ s
      · simpa [F, h'] using isOpen_interior
      · simpa [F, h'] using (isOpen_empty : IsOpen (∅ : Set (β a')))
    -- Turn it into a set of Σ.
    let W : Set (Sigma β) := {q | q.2 ∈ F q.1}
    have hW_open : IsOpen W := by
      -- Use the characterisation of open sets in Σ–types.
      refine (isOpen_sigma_iff).2 ?_
      intro a'
      have : {b'' : β a' | (⟨a', b''⟩ : Sigma β) ∈ W} = F a' := rfl
      simpa [this] using hF_open a'
    -- `W` is contained in `S`.
    have hW_sub : W ⊆ S := by
      intro q hq
      rcases q with ⟨a', b''⟩
      dsimp [W] at hq
      by_cases hsa' : a' ∈ s
      · -- Here `F a' = interior (t a')`.
        have hFdef : F a' = interior (t a') := by
          simp [F, hsa'] at *
        have hb''int : b'' ∈ interior (t a') := by
          simpa [hFdef] using hq
        exact And.intro hsa' (interior_subset hb''int)
      · -- Otherwise `F a' = ∅`, contradiction.
        have : b'' ∈ (∅ : Set (β a')) := by
          simpa [F, hsa'] using hq
        cases this
    -- The constructed point lies in `W`.
    have hqW : (⟨a, b'⟩ : Sigma β) ∈ W := by
      dsimp [W]
      have hFdef : F a = interior (t a) := by
        have : a ∈ s := ha
        simp [F, this]
      simpa [hFdef] using hb'int
    -- Since `W ⊆ S` and `W` is open, points of `W` are in `interior S`.
    have hsubsetW : (W : Set (Sigma β)) ⊆ interior S :=
      interior_maximal hW_sub hW_open
    have hq_intS : (⟨a, b'⟩ : Sigma β) ∈ interior S := hsubsetW hqW
    -- `(a , b')` is also in `U`.
    have hqU : (⟨a, b'⟩ : Sigma β) ∈ U := by
      have : b' ∈ V := hb'V
      simpa [V] using this
    -- Provide the witness required by the closure criterion.
    exact ⟨⟨a, b'⟩, hqU, hq_intS⟩
  -- Finish: unravel `S`.
  simpa [S] using h_cl