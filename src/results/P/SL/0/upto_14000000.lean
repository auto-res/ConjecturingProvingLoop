

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  dsimp [Topology.P2, Topology.P1] at *
  exact h.trans interior_subset

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hA
  dsimp [Topology.P2, Topology.P3] at hA ⊢
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono hcl
  exact hA.trans hmono

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro h
  exact ⟨P2_implies_P1 h, P2_implies_P3 h⟩

theorem interior_has_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  -- We want `interior A ⊆ interior (closure (interior (interior A)))`.
  -- Since `interior (interior A) = interior A`, this is the same as
  -- `interior A ⊆ interior (closure (interior A))`, which follows from
  -- `interior_mono` applied to `subset_closure`.
  have h : interior A ⊆ interior (closure (interior A)) := by
    have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono subset_closure
    simpa [interior_interior] using h'
  simpa [interior_interior] using h

theorem interior_has_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ∧ Topology.P3 (interior A) := by
  have hP2 : Topology.P2 (interior A) := by
    simpa using (interior_has_P2 (X := X) (A := A))
  have hP1 : Topology.P1 (interior A) := (P2_implies_P1 (X := X) (A := interior A)) hP2
  have hP3 : Topology.P3 (interior A) := (P2_implies_P3 (X := X) (A := interior A)) hP2
  exact And.intro hP1 hP3

theorem P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  dsimp [Topology.P2, Topology.P3]
  simpa [hA.interior_eq]

theorem isOpen_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- First establish `P2` for the open set `A`.
  have hP2 : Topology.P2 A := by
    dsimp [Topology.P2]
    have hsubset : (A : Set X) ⊆ interior (closure A) := by
      have hcl : (A : Set X) ⊆ closure A := subset_closure
      exact interior_maximal hcl hA
    simpa [hA.interior_eq] using hsubset
  -- Derive `P1` and `P3` from `P2`.
  have hP1 : Topology.P1 A := (P2_implies_P1 (X := X) (A := A)) hP2
  have hP3 : Topology.P3 A := (P2_implies_P3 (X := X) (A := A)) hP2
  exact ⟨hP1, hP2, hP3⟩

theorem interior_closure_has_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  have hAll := Topology.isOpen_has_all_Ps (X := X) (A := interior (closure A)) hOpen
  exact hAll.2.1

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  -- `P2` holds for every open set.
  have hP2_open : Topology.P2 A := by
    dsimp [Topology.P2]
    have hsubset : (A : Set X) ⊆ interior (closure A) := by
      have hcl : (A : Set X) ⊆ closure A := subset_closure
      exact interior_maximal hcl hA
    simpa [hA.interior_eq] using hsubset
  -- Construct the equivalence.
  constructor
  · intro _
    exact hP2_open
  · intro hP2
    exact (Topology.P2_implies_P1 (X := X) (A := A)) hP2

theorem interior_closure_has_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) ∧ Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  have hAll := Topology.isOpen_has_all_Ps (X := X) (A := interior (closure A)) hOpen
  exact And.intro hAll.1 hAll.2.2

theorem P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  -- First, `closure A ⊆ closure (interior A)` by monotonicity of `closure`.
  have h₁ : closure A ⊆ closure (interior A) := by
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa using this
  -- Next, `closure (interior A) ⊆ closure (interior (closure A))` as
  -- `interior A ⊆ interior (closure A)`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    exact interior_mono subset_closure
  -- Putting the two inclusions together yields the desired result.
  exact h₁.trans h₂

theorem interior_closure_interior_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) ∧
    Topology.P2 (interior (closure (interior A))) ∧
    Topology.P3 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  have hAll :=
    Topology.isOpen_has_all_Ps (X := X) (A := interior (closure (interior A))) hOpen
  simpa using hAll

theorem P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  exact h₁.trans h₂

theorem interior_subset_interior_closure_inter {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior A : Set X) ⊆ interior (closure (interior A)) := by
  have h : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  simpa using interior_mono h

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure (A : Set X) = closure (interior A) := by
  dsimp [Topology.P1]
  constructor
  · intro hP1
    have h₁ : closure A ⊆ closure (interior A) := by
      simpa using (closure_mono hP1)
    have h₂ : closure (interior A) ⊆ closure A := by
      exact closure_mono (interior_subset : interior A ⊆ A)
    exact subset_antisymm h₁ h₂
  · intro hEq
    have hA : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq] using hA

theorem closure_interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  have hP1_int : Topology.P1 (interior A) :=
    (interior_has_P1_and_P3 (X := X) (A := A)).1
  exact (P1_implies_P1_closure (X := X) (A := interior A)) hP1_int

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (A : Set X) = closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A := (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  exact (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1

theorem closure_interior_closure_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  -- `interior (closure A)` is open, hence it satisfies `P1`.
  have hP1_int : Topology.P1 (interior (closure A)) := by
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    exact (Topology.isOpen_has_all_Ps (X := X) (A := interior (closure A)) hOpen).1
  -- Property `P1` is preserved under taking closures.
  exact (Topology.P1_implies_P1_closure (X := X) (A := interior (closure A))) hP1_int

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at hA hB ⊢
  -- `A` is contained in the target set.
  have hA' : (A : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hMono : closure (interior A : Set X) ⊆ closure (interior (A ∪ B)) := by
      apply closure_mono
      exact interior_mono (Set.subset_union_left)
    exact hA.trans hMono
  -- `B` is contained in the target set.
  have hB' : (B : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hMono : closure (interior B : Set X) ⊆ closure (interior (A ∪ B)) := by
      apply closure_mono
      exact interior_mono (Set.subset_union_right)
    exact hB.trans hMono
  -- Combine the two inclusions.
  intro x hx
  cases hx with
  | inl hxA => exact hA' hxA
  | inr hxB => exact hB' hxB

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_in : x ∈ interior (closure A) := hA hxA
      have hMono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have : closure A ⊆ closure (A ∪ B) := by
          simpa using closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact interior_mono this
      exact hMono hx_in
  | inr hxB =>
      -- `x` comes from `B`
      have hx_in : x ∈ interior (closure B) := hB hxB
      have hMono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have : closure B ⊆ closure (A ∪ B) := by
          simpa using closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact interior_mono this
      exact hMono hx_in

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_in : x ∈ interior (closure (interior A)) := hA hxA
      have hMono : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hIntSub : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        have hClSub : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hIntSub
        exact interior_mono hClSub
      exact hMono hx_in
  | inr hxB =>
      have hx_in : x ∈ interior (closure (interior B)) := hB hxB
      have hMono : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hIntSub : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        have hClSub : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hIntSub
        exact interior_mono hClSub
      exact hMono hx_in

theorem P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 A ↔ IsOpen (A : Set X) := by
  dsimp [Topology.P3]
  have h_closure : closure (A : Set X) = A := hA.closure_eq
  constructor
  · intro hP3
    have h_subset : (A : Set X) ⊆ interior A := by
      simpa [h_closure] using hP3
    have h_eq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact h_subset
    simpa [h_eq] using
      (isOpen_interior : IsOpen (interior (A : Set X)))
  · intro hOpen
    exact (Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen).2.2

theorem P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP1 : Topology.P1 A := (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  exact (Topology.P1_implies_P1_closure (X := X) (A := A)) hP1

theorem P1_iff_eq_closure_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    Topology.P1 A ↔ (A : Set X) = closure (interior A) := by
  have h_cl : closure (A : Set X) = A := hA.closure_eq
  have h₁ : Topology.P1 A ↔ closure (A : Set X) = closure (interior A) :=
    Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  simpa [h_cl] using h₁

theorem P1_implies_interior_closure_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP1
  have hEq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  simpa [hEq]

theorem P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 A ↔ IsOpen (A : Set X) := by
  dsimp [Topology.P2]
  constructor
  · intro hP2
    -- First, `closure (interior A)` is contained in `A` since `A` is closed.
    have hcl : closure (interior (A : Set X)) ⊆ (A : Set X) := by
      have : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
        closure_mono (interior_subset : interior (A : Set X) ⊆ A)
      simpa [hA.closure_eq] using this
    -- Hence the target of `hP2` is contained in `interior A`.
    have hsubset : (A : Set X) ⊆ interior (A : Set X) := by
      have hmono : interior (closure (interior (A : Set X))) ⊆ interior (A : Set X) :=
        interior_mono hcl
      exact hP2.trans hmono
    -- `A` equals its interior, so it is open.
    have h_eq : interior (A : Set X) = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact hsubset
    simpa [h_eq] using (isOpen_interior : IsOpen (interior (A : Set X)))
  · intro hOpen
    exact (Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen).2.1

theorem P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [hOpen.interior_eq] using hx_cl

theorem empty_has_all_Ps {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  have hOpen : IsOpen (∅ : Set X) := isOpen_empty
  exact Topology.isOpen_has_all_Ps (X := X) (A := (∅ : Set X)) hOpen

theorem P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h₁ : Topology.P2 A ↔ IsOpen (A : Set X) :=
    Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA
  have h₂ : Topology.P3 A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA
  exact h₁.trans h₂.symm

theorem univ_has_all_Ps {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  exact Topology.isOpen_has_all_Ps (X := X) (A := (Set.univ : Set X)) hOpen

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  -- The interior of `closure A` is the whole space since `closure A = univ`.
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hDense] using interior_univ
  -- Hence any point, in particular `x`, lies in `interior (closure A)`.
  have : x ∈ interior (closure (A : Set X)) := by
    simpa [hInt] using (by
      simp : x ∈ (Set.univ : Set X))
  exact this

theorem closure_interior_closure_interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior A)))) := by
  have hP1 : Topology.P1 (interior (closure (interior A))) :=
    (Topology.interior_closure_interior_has_all_Ps (X := X) (A := A)).1
  exact (Topology.P1_implies_P1_closure (X := X) (A := interior (closure (interior A)))) hP1

theorem interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) ⊆ interior (closure (A : Set X)) := by
  have hcl : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  exact interior_mono hcl

theorem P3_iUnion {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (∀ i, Topology.P3 (F i)) → Topology.P3 (⋃ i, F i) := by
  intro hF
  dsimp [Topology.P3] at hF ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxFi⟩
  have hx_int : x ∈ interior (closure (F i : Set X)) := hF i hxFi
  have h_mono : interior (closure (F i : Set X)) ⊆
      interior (closure (⋃ j, F j : Set X)) := by
    have h_clos : closure (F i : Set X) ⊆ closure (⋃ j, F j : Set X) := by
      have h_subset : (F i : Set X) ⊆ ⋃ j, F j := Set.subset_iUnion _ _
      exact closure_mono h_subset
    exact interior_mono h_clos
  exact h_mono hx_int

theorem P2_iUnion {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (∀ i, Topology.P2 (F i)) → Topology.P2 (⋃ i, F i) := by
  intro hF
  dsimp [Topology.P2] at hF ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxFi⟩
  have hx_in : x ∈ interior (closure (interior (F i : Set X))) := hF i hxFi
  have h_mono : interior (closure (interior (F i : Set X))) ⊆
      interior (closure (interior (⋃ j, F j : Set X))) := by
    have h_int_sub : interior (F i : Set X) ⊆ interior (⋃ j, F j : Set X) :=
      interior_mono (Set.subset_iUnion _ _)
    have h_cl_sub : closure (interior (F i : Set X)) ⊆
        closure (interior (⋃ j, F j : Set X)) := closure_mono h_int_sub
    exact interior_mono h_cl_sub
  exact h_mono hx_in

theorem P1_iUnion {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (∀ i, Topology.P1 (F i)) → Topology.P1 (⋃ i, F i) := by
  intro hF
  dsimp [Topology.P1] at hF ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxFi⟩
  have hx_cl : x ∈ closure (interior (F i : Set X)) := hF i hxFi
  have h_mono : closure (interior (F i : Set X)) ⊆
      closure (interior (⋃ j, F j : Set X)) := by
    have h_int_sub : interior (F i : Set X) ⊆ interior (⋃ j, F j : Set X) :=
      interior_mono (Set.subset_iUnion _ _)
    exact closure_mono h_int_sub
  exact h_mono hx_cl

theorem interior_has_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  exact (Topology.interior_has_P1_and_P3 (X := X) (A := A)).2

theorem interior_closure_interior_idempotent {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  -- First inclusion: left ⊆ right.
  have h₁ :
      interior (closure (interior (closure (interior A)))) ⊆
        interior (closure (interior A)) := by
    simpa [closure_closure] using
      (Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure (interior A)))
  -- Second inclusion: right ⊆ left.
  have h₂ :
      interior (closure (interior A)) ⊆
        interior (closure (interior (closure (interior A)))) := by
    have hSub :
        (interior (closure (interior A)) : Set X) ⊆
          closure (interior (closure (interior A))) := subset_closure
    have hOpen : IsOpen (interior (closure (interior A)) : Set X) :=
      isOpen_interior
    exact interior_maximal hSub hOpen
  exact subset_antisymm h₁ h₂

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (closure (A ∪ B)) := by
  intro hA hB
  have h_union : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  have h_closure : Topology.P1 (closure (A ∪ B)) :=
    Topology.P1_implies_P1_closure (X := X) (A := A ∪ B) h_union
  simpa using h_closure

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (A : Set X) = closure (interior A) := by
  intro hP1
  exact ((Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A))).1 hP1

theorem P3_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hPA hPB
  -- Convert `P3` for `A` and `B` into openness, using the closed–open equivalence.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := B) hB).1 hPB
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Every open set satisfies `P3`.
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B : Set X)) hOpenInter).2.2

theorem interior_closure_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (A : Set X))) ∧
    Topology.P2 (interior (closure (A : Set X))) ∧
    Topology.P3 (interior (closure (A : Set X))) := by
  -- Obtain `P1` and `P3` for `interior (closure A)`.
  have hP1P3 := Topology.interior_closure_has_P1_and_P3 (X := X) (A := A)
  -- Obtain `P2` for `interior (closure A)`.
  have hP2 := Topology.interior_closure_has_P2 (X := X) (A := A)
  -- Assemble the triple conjunction.
  exact And.intro hP1P3.1 (And.intro hP2 hP1P3.2)

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (closure (A : Set X))) := by
  -- Since `A ⊆ closure A`, monotonicity of `interior` gives the key inclusion.
  have h : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
  -- Taking `closure` on both sides preserves the inclusion.
  exact closure_mono h

theorem P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := closure (A : Set X)) hClosed)

theorem P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := closure (A : Set X)) hClosed)

theorem P2_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hPA hPB
  -- Translate `P2` for the closed sets `A` and `B` into openness.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := B) hB).1 hPB
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Every open set satisfies `P2`.
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B : Set X)) hOpenInter).2.1

theorem P2_implies_interior_closure_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  exact
    (Topology.P1_implies_interior_closure_eq_interior_closure_interior
        (X := X) (A := A)) hP1

theorem P2_iff_P3_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P3 (closure (A : Set X)) := by
  have h₁ : Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) :=
    Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
  have h₂ : Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) :=
    Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  exact h₁.trans h₂.symm

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) → Topology.P2 A := by
  intro hOpen
  have hAll := Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen
  exact hAll.2.1

theorem isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) → Topology.P1 A := by
  intro hOpen
  exact (Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen).1

theorem isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) → Topology.P3 A := by
  intro hOpen
  have hAll := Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen
  exact hAll.2.2

theorem P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hP3_cl
  -- From `P3` for `closure A` we deduce that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv :=
      (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A))
    exact (hEquiv).1 hP3_cl
  -- An open `closure A` directly yields `P3` for `A`.
  exact (Topology.P3_of_isOpen_closure (X := X) (A := A)) hOpen

theorem P1_implies_P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (interior A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  have hxA : (x : X) ∈ (A : Set X) := interior_subset hx
  have : x ∈ closure (interior A) := hP1 hxA
  simpa [interior_interior] using this

theorem P1_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B : Set X)) hOpen).1

theorem interior_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (A : Set X)) ∧
    Topology.P2 (interior (A : Set X)) ∧
    Topology.P3 (interior (A : Set X)) := by
  -- `P1` and `P3` for `interior A` are already bundled together.
  have hP1P3 := Topology.interior_has_P1_and_P3 (X := X) (A := A)
  -- `P2` for `interior A` is provided separately.
  have hP2 := Topology.interior_has_P2 (X := X) (A := A)
  -- Combine the three properties.
  exact And.intro hP1P3.1 (And.intro hP2 hP1P3.2)

theorem P2_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B : Set X)) hOpen).2.1

theorem P2_implies_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → (A : Set X) ⊆ interior (closure A) := by
  intro hP2
  dsimp [Topology.P2] at hP2
  have hmono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    have hcl : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    exact interior_mono hcl
  exact hP2.trans hmono

theorem P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hP3
  exact (Topology.isOpen_implies_P1 (X := X) (A := A)) hOpen

theorem P2_and_isClosed_iff_clopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P2 A ∧ IsClosed (A : Set X)) ↔ (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  constructor
  · rintro ⟨hP2, hClosed⟩
    have hOpen : IsOpen (A : Set X) :=
      ((Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP2
    exact ⟨hOpen, hClosed⟩
  · rintro ⟨hOpen, hClosed⟩
    have hP2 : Topology.P2 A :=
      (Topology.isOpen_implies_P2 (X := X) (A := A)) hOpen
    exact ⟨hP2, hClosed⟩

theorem P3_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B : Set X)) hOpen).2.2

theorem isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hOpen
  dsimp [Topology.P1]
  -- Step 1:  Show `A ⊆ interior (closure A)`.
  have hA_sub : (A : Set X) ⊆ interior (closure (A : Set X)) := by
    intro x hxA
    -- Since `A` is open, `x` is an interior point of `A`.
    have hxIntA : x ∈ interior (A : Set X) := by
      simpa [hOpen.interior_eq] using hxA
    -- Monotonicity of `interior` gives the desired inclusion.
    have hMono : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
    exact hMono hxIntA
  -- Step 2: Take closures to obtain the required inclusion.
  have hClosure :
      (closure (A : Set X) : Set X) ⊆ closure (interior (closure (A : Set X))) :=
    closure_mono hA_sub
  exact hClosure

theorem P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  dsimp [Topology.P3, Topology.P1] at hP3 ⊢
  exact closure_mono hP3

theorem P3_and_isClosed_iff_clopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P3 A ∧ IsClosed (A : Set X)) ↔
      (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  constructor
  · rintro ⟨hP3, hClosed⟩
    have hOpen : IsOpen (A : Set X) :=
      ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP3
    exact ⟨hOpen, hClosed⟩
  · rintro ⟨hOpen, hClosed⟩
    have hP3 : Topology.P3 A :=
      ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).2) hOpen
    exact ⟨hP3, hClosed⟩

theorem P2_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (Aᶜ) := by
  have hOpen : IsOpen ((Aᶜ) : Set X) := hA.isOpen_compl
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (Aᶜ : Set X)) hOpen).2.1

theorem P3_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen ((Aᶜ) : Set X) := hA.isOpen_compl
  exact (Topology.isOpen_implies_P3 (X := X) (A := (Aᶜ : Set X))) hOpen

theorem closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (A : Set X)))) =
      closure (interior (A : Set X)) := by
  apply subset_antisymm
  · -- Left ⊆ right.
    have h :
        interior (closure (interior (A : Set X))) ⊆
          closure (interior (A : Set X)) := interior_subset
    have h' := closure_mono h
    simpa [closure_closure] using h'
  · -- Right ⊆ left, using the monotonicity lemma with `A := interior A`.
    have h :=
      Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := interior (A : Set X))
    simpa [interior_interior] using h

theorem P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2_cl
  -- From `P2` for `closure A` we deduce that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv :=
      (Topology.P2_closure_iff_isOpen_closure (X := X) (A := A))
    exact (hEquiv).1 hP2_cl
  -- An open `closure A` directly yields `P3` for `A`.
  exact (Topology.P3_of_isOpen_closure (X := X) (A := A)) hOpen

theorem P1_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P1 (Aᶜ) := by
  have hOpen : IsOpen ((Aᶜ) : Set X) := hA.isOpen_compl
  exact (Topology.isOpen_implies_P1 (X := X) (A := (Aᶜ : Set X))) hOpen

theorem clopen_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- We can obtain all three properties directly from the fact that `A` is open.
  exact Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen

theorem closure_interior_subset_closure_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure (A : Set X) := by
  exact closure_mono (interior_subset : interior (A : Set X) ⊆ A)

theorem closure_interior_closure_interior_closure_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  simpa using
    (closure_interior_closure_interior_idempotent
      (X := X) (A := closure (A : Set X)))

theorem P3_implies_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (A : Set X) ⊆ interior (closure (A : Set X)) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  simpa using hP3

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, combine `A` and `B` using the existing two‐set union lemma.
  have hAB : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Next, unite the result with `C`.
  have hABC : Topology.P1 ((A ∪ B) ∪ C) :=
    Topology.P1_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Use associativity of `∪` to rewrite the goal.
  simpa [Set.union_assoc] using hABC

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have hInt : interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hDense] using interior_univ
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using hx_univ

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 C → Topology.P3 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, union `A` and `B`.
  have hAB : Topology.P3 (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Topology.P3 ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABC

theorem P3_closure_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hP3_cl
  -- From `P3` for `closure A` we deduce that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv :=
      (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A))
    exact (hEquiv).1 hP3_cl
  -- Every open set, in particular `closure A`, satisfies `P2`.
  exact (Topology.isOpen_implies_P2 (X := X) (A := closure (A : Set X))) hOpen

theorem interior_closure_eq_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) =
      interior (closure (interior (closure (A : Set X)))) := by
  -- First inclusion: `interior (closure A) ⊆ interior (closure (interior (closure A)))`.
  have h₁ :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure (A : Set X))) := subset_closure
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  have h_left :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) :=
    interior_maximal h₁ hOpen
  -- Second inclusion: `interior (closure (interior (closure A))) ⊆ interior (closure A)`.
  have h_right :
      (interior (closure (interior (closure (A : Set X)))) : Set X) ⊆
        interior (closure (A : Set X)) := by
    -- This is an instance of the monotonicity lemma with `A := closure A`.
    simpa [closure_closure] using
      (Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure (A : Set X)))
  exact Set.Subset.antisymm h_left h_right

theorem P1_implies_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  have hcl :
      closure (interior (A : Set X)) ⊆ closure (interior (closure (A : Set X))) := by
    apply closure_mono
    have : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
    exact this
  exact hP1.trans hcl

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1] at *
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hDense] using this

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, unite `A` and `B`.
  have hAB : Topology.P2 (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  -- Next, unite the result with `C`.
  have hABC : Topology.P2 ((A ∪ B) ∪ C) :=
    Topology.P2_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABC

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro h𝒜
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure (A : Set X)) := h𝒜 A hA_mem hxA
  have h_mono :
      interior (closure (A : Set X)) ⊆
        interior (closure (⋃₀ 𝒜 : Set X)) := by
    have h_closure :
        closure (A : Set X) ⊆ closure (⋃₀ 𝒜 : Set X) := by
      have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_mono hx_int

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro h𝒜
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hx_cl : x ∈ closure (interior (A : Set X)) := h𝒜 A hA_mem hxA
  have h_mono :
      closure (interior (A : Set X)) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) := by
    have h_int_sub :
        interior (A : Set X) ⊆ interior (⋃₀ 𝒜 : Set X) := by
      have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact interior_mono h_sub
    exact closure_mono h_int_sub
  exact h_mono hx_cl

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro h𝒜
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hx_in : x ∈ interior (closure (interior (A : Set X))) :=
    h𝒜 A hA_mem hxA
  have h_subset : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
  have h_int_sub :
      interior (A : Set X) ⊆ interior (⋃₀ 𝒜 : Set X) :=
    interior_mono h_subset
  have h_closure_sub :
      closure (interior (A : Set X)) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) :=
    closure_mono h_int_sub
  have h_mono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (interior (⋃₀ 𝒜 : Set X))) :=
    interior_mono h_closure_sub
  exact h_mono hx_in

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) := by
  exact interior_mono (closure_mono hAB)

theorem interior_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure (A : Set X)) := by
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))

theorem P3_inter_three_of_open {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    Topology.P3 (A ∩ B ∩ C) := by
  -- The triple intersection of open sets is open.
  have hOpen : IsOpen ((A ∩ B ∩ C) : Set X) := (hA.inter hB).inter hC
  -- Every open set satisfies `P3`.
  exact
    (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B ∩ C : Set X)) hOpen).2.2

theorem P3_inter_three_of_closed {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) (hC : IsClosed (C : Set X)) :
    Topology.P3 A → Topology.P3 B → Topology.P3 C → Topology.P3 (A ∩ B ∩ C) := by
  intro hPA hPB hPC
  -- Convert each `P3` on a closed set into openness.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := B) hB).1 hPB
  have hOpenC : IsOpen (C : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := C) hC).1 hPC
  -- The triple intersection of open sets is open.
  have hOpenInter : IsOpen ((A ∩ B ∩ C) : Set X) := (hOpenA.inter hOpenB).inter hOpenC
  -- Every open set satisfies `P3`.
  exact
    (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B ∩ C : Set X)) hOpenInter).2.2

theorem P2_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hP2_cl
  -- From `P2` for `closure A` we deduce that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv := Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
    exact (hEquiv).1 hP2_cl
  -- Every open set, in particular `closure A`, satisfies `P1`.
  exact (Topology.isOpen_implies_P1 (X := X) (A := closure (A : Set X))) hOpen

theorem P2_inter_three_of_open {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    Topology.P2 (A ∩ B ∩ C) := by
  have hOpen : IsOpen ((A ∩ B ∩ C) : Set X) := (hA.inter hB).inter hC
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B ∩ C : Set X)) hOpen).2.1

theorem P1_inter_three_of_open {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    Topology.P1 (A ∩ B ∩ C) := by
  have hOpen : IsOpen ((A ∩ B ∩ C) : Set X) := (hA.inter hB).inter hC
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B ∩ C : Set X)) hOpen).1

theorem closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) := by
  exact closure_mono (interior_mono hAB)

theorem interior_closure_closure_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure (A : Set X))) =
      interior (closure (A : Set X)) := by
  simpa [closure_closure]

theorem P2_inter_three_of_closed {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) (hC : IsClosed (C : Set X)) :
    Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 (A ∩ B ∩ C) := by
  intro hPA hPB hPC
  -- Translate each `P2` on a closed set into openness.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := B) hB).1 hPB
  have hOpenC : IsOpen (C : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := C) hC).1 hPC
  -- The triple intersection of open sets is open.
  have hOpenInter : IsOpen ((A ∩ B ∩ C) : Set X) := (hOpenA.inter hOpenB).inter hOpenC
  -- Every open set satisfies `P2`.
  exact
    (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B ∩ C : Set X)) hOpenInter).2.1

theorem P2_implies_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      (A : Set X) ⊆ interior (closure (interior (closure (A : Set X)))) := by
  intro hP2
  -- Step 1 : `A ⊆ interior (closure A)` using an existing lemma.
  have h₁ :
      (A : Set X) ⊆ interior (closure (A : Set X)) :=
    Topology.P2_implies_subset_interior_closure (X := X) (A := A) hP2
  -- Step 2 : `interior (closure A)` is open, hence satisfies `P2`,
  -- giving the desired nested inclusion.
  have h₂ :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) := by
    -- `interior (closure A)` is open.
    have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    -- Every open set satisfies `P2`.
    have hP2' :
        Topology.P2 (interior (closure (A : Set X))) :=
      Topology.isOpen_implies_P2 (X := X)
        (A := interior (closure (A : Set X))) hOpen
    -- Unpack the definition of `P2`.
    dsimp [Topology.P2] at hP2'
    simpa using hP2'
  -- Combine the two inclusions.
  intro x hxA
  have hxB : x ∈ interior (closure (A : Set X)) := h₁ hxA
  exact h₂ hxB

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x _
  -- The interior of `closure (interior A)` is the whole space.
  have hIntUniv :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hDense] using interior_univ
  -- By monotonicity, `interior (closure (interior A)) ⊆ interior (closure A)`.
  have hMono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    have hcl :
        closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    exact interior_mono hcl
  -- Any point belongs to `interior (closure A)` since it equals the whole space.
  have hxInt : x ∈ interior (closure (A : Set X)) := by
    have hxUniv : (x : X) ∈ (Set.univ : Set X) := by
      simp
    have hxInt' :
        x ∈ interior (closure (interior (A : Set X))) := by
      simpa [hIntUniv] using hxUniv
    exact hMono hxInt'
  exact hxInt

theorem P3_implies_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 A → Topology.P2 A := by
  intro hP3
  exact
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hA).mpr hP3

theorem interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (A : Set X)) := by
  exact (Topology.interior_has_P1_and_P3 (X := X) (A := A)).1

theorem closure_interior_interior_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior (A : Set X))) =
      closure (interior (A : Set X)) := by
  simpa [interior_interior]

theorem interior_closure_inter_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure ((A ∩ B) : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  -- First, relate `closure (A ∩ B)` to `closure A` and `closure B`.
  have hSubA :
      closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
    have hAB_SubA : (A ∩ B : Set X) ⊆ (A : Set X) := by
      intro x hx
      exact hx.1
    exact closure_mono hAB_SubA
  have hSubB :
      closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
    have hAB_SubB : (A ∩ B : Set X) ⊆ (B : Set X) := by
      intro x hx
      exact hx.2
    exact closure_mono hAB_SubB
  -- Use monotonicity of `interior` to obtain the desired inclusions.
  have hIntSubA :
      interior (closure ((A ∩ B) : Set X)) ⊆
        interior (closure (A : Set X)) := interior_mono hSubA
  have hIntSubB :
      interior (closure ((A ∩ B) : Set X)) ⊆
        interior (closure (B : Set X)) := interior_mono hSubB
  -- Combine the two inclusions.
  intro x hx
  exact And.intro (hIntSubA hx) (hIntSubB hx)

theorem interior_closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (interior (closure (A : Set X)) ∪ interior (closure (B : Set X))) ⊆
      interior (closure (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure A)`.
      have hMono : interior (closure (A : Set X)) ⊆
          interior (closure (A ∪ B : Set X)) := by
        have hCl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) :=
          closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact interior_mono hCl
      exact hMono hxA
  | inr hxB =>
      -- Handle the case `x ∈ interior (closure B)`.
      have hMono : interior (closure (B : Set X)) ⊆
          interior (closure (A ∪ B : Set X)) := by
        have hCl : closure (B : Set X) ⊆ closure (A ∪ B : Set X) :=
          closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact interior_mono hCl
      exact hMono hxB

theorem closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) := by
  simpa [closure_closure] using
    (closure_interior_subset_closure_self
      (X := X) (A := closure (A : Set X)))

theorem interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (A : Set X).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP3 hA
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  simpa using (Topology.empty_has_all_Ps (X := X)).1

theorem P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  exact (Topology.empty_has_all_Ps (X := X)).2.2

theorem P1_closure_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C →
      Topology.P1 (closure ((A ∪ B ∪ C) : Set X)) := by
  intro hA hB hC
  -- First, `P1` for the triple union.
  have hUnion : Topology.P1 (A ∪ B ∪ C) :=
    Topology.P1_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Taking the closure preserves `P1`.
  have hClosure : Topology.P1 (closure ((A ∪ B ∪ C) : Set X)) :=
    Topology.P1_implies_P1_closure (X := X) (A := A ∪ B ∪ C) hUnion
  simpa using hClosure

theorem interior_closure_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A : Set X).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP2 hA
  rcases hA with ⟨x, hxA⟩
  -- From `P2` we know `A ⊆ interior (closure A)`.
  have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) :=
    Topology.P2_implies_subset_interior_closure (X := X) (A := A) hP2
  -- The chosen point `x` of `A` therefore lies in `interior (closure A)`.
  exact ⟨x, hSub hxA⟩

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    dsimp [Topology.P1] at hP1
    have h : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using h
  · intro hSub
    dsimp [Topology.P1]
    intro x hxA
    have hxCl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    exact hSub hxCl

theorem interior_closure_interior_closure_has_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior (closure A)))) := by
  -- The set `interior (closure (interior (closure A)))` is open, so it satisfies `P2`.
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  have hAll :=
    Topology.isOpen_has_all_Ps
      (X := X) (A := interior (closure (interior (closure A)))) hOpen
  exact hAll.2.1

theorem P2_implies_P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P2 (interior A) := by
  intro _
  simpa using (Topology.interior_has_P2 (X := X) (A := A))

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  simpa using ((Topology.univ_has_all_Ps (X := X)).2.1)

theorem P3_of_interior_closure_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (closure (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3] at *
  intro x _
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using hx_univ

theorem interior_closure_has_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (A : Set X))) := by
  exact (Topology.interior_closure_has_P1_and_P3 (X := X) (A := A)).2

theorem P2_implies_P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  exact (Topology.P1_implies_P1_interior (X := X) (A := A)) hP1

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  simpa using ((Topology.univ_has_all_Ps (X := X)).2.2)

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  simpa using ((Topology.univ_has_all_Ps (X := X)).1)

theorem P2_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → IsOpen (B : Set X) → Topology.P2 (A ∪ B) := by
  intro hP2A hOpenB
  -- An open set automatically satisfies `P2`.
  have hP2B : Topology.P2 B :=
    Topology.isOpen_implies_P2 (X := X) (A := B) hOpenB
  -- Combine the two sets using the existing union lemma for `P2`.
  exact Topology.P2_union (X := X) (A := A) (B := B) hP2A hP2B

theorem P2_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen (A : Set X) → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hOpenA hP2B
  -- An open set automatically satisfies `P2`.
  have hP2A : Topology.P2 A :=
    Topology.isOpen_implies_P2 (X := X) (A := A) hOpenA
  -- Combine the two sets using the existing union lemma for `P2`.
  exact Topology.P2_union (X := X) (A := A) (B := B) hP2A hP2B

theorem interior_closure_iInter_subset_iInter_interiors {X ι : Type*}
    [TopologicalSpace X] {F : ι → Set X} :
    interior (closure (⋂ i, F i : Set X)) ⊆
      (⋂ i, interior (closure (F i : Set X))) := by
  intro x hx
  -- We show that `x` belongs to every `interior (closure (F i))`.
  refine Set.mem_iInter.2 ?_
  intro i
  -- Monotonicity: `closure (⋂ i, F i) ⊆ closure (F i)`.
  have h_closure : closure (⋂ j, F j : Set X) ⊆ closure (F i : Set X) := by
    have h_subset : (⋂ j, F j : Set X) ⊆ (F i : Set X) :=
      Set.iInter_subset (fun j ↦ F j) i
    exact closure_mono h_subset
  -- Applying `interior` preserves the inclusion.
  have h_interior :
      interior (closure (⋂ j, F j : Set X)) ⊆
        interior (closure (F i : Set X)) := interior_mono h_closure
  exact h_interior hx

theorem P2_implies_closure_subset_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (A : Set X) ⊆ closure (interior (closure (interior A))) := by
  intro hP2
  dsimp [Topology.P2] at hP2
  exact closure_mono hP2

theorem closure_subset_closure_union_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    closure (A : Set X) ⊆ closure (A ∪ B ∪ C : Set X) := by
  -- The set `A` is contained in `A ∪ B ∪ C`.
  have hSub : (A : Set X) ⊆ A ∪ B ∪ C := by
    intro x hx
    exact Or.inl (Or.inl hx)
  -- Taking closures preserves the inclusion.
  exact closure_mono hSub

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  simpa using (Topology.empty_has_all_Ps (X := X)).2.1



theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X).Nonempty → (interior (A : Set X)).Nonempty := by
  classical
  intro hP1 hA
  rcases hA with ⟨x, hxA⟩
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  by_cases hIntEmpty : interior (A : Set X) = (∅ : Set X)
  · -- This case contradicts the membership `hx_cl`.
    have : x ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty] using hx_cl
    exact (this.elim)
  · -- If `interior A` is not empty, we are done.
    exact (Set.nonempty_iff_ne_empty).2 hIntEmpty

theorem closure_interior_closure_eq_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A →
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  intro hP3
  -- `closure A` is contained in `closure (interior (closure A))` by `P3`.
  have h₁ : closure (A : Set X) ⊆
      closure (interior (closure (A : Set X))) := by
    have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    exact closure_mono hSub
  -- The reverse inclusion holds by monotonicity of `closure`.
  have h₂ :
      closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
    Topology.closure_interior_closure_subset_closure (X := X) (A := A)
  exact subset_antisymm h₂ h₁

theorem P1_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → IsOpen (B : Set X) → Topology.P1 (A ∪ B) := by
  intro hP1A hOpenB
  -- An open set automatically satisfies `P1`.
  have hP1B : Topology.P1 B :=
    Topology.isOpen_implies_P1 (X := X) (A := B) hOpenB
  -- Combine the two sets using the existing union lemma for `P1`.
  exact Topology.P1_union (X := X) (A := A) (B := B) hP1A hP1B

theorem P3_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → IsOpen (B : Set X) → Topology.P3 (A ∪ B) := by
  intro hP3A hOpenB
  -- An open set automatically satisfies `P3`.
  have hP3B : Topology.P3 B :=
    Topology.isOpen_implies_P3 (X := X) (A := B) hOpenB
  -- Combine the two sets using the existing union lemma for `P3`.
  exact Topology.P3_union (X := X) (A := A) (B := B) hP3A hP3B

theorem P3_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P3 (closure (A : Set X)) := by
  intro hOpen
  have hEquiv := Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  exact (hEquiv).2 hOpen

theorem P1_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen (A : Set X) → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hOpenA hP1B
  -- An open set automatically satisfies `P1`.
  have hP1A : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hOpenA
  -- Combine the two sets using the existing union lemma for `P1`.
  exact Topology.P1_union (X := X) (A := A) (B := B) hP1A hP1B

theorem interior_closure_interior_closure_has_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior (closure A)))) := by
  -- The set in question is open, hence it satisfies `P3`.
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  exact
    (Topology.isOpen_has_all_Ps
        (X := X)
        (A := interior (closure (interior (closure A))))
        hOpen).2.2

theorem interior_closure_interior_closure_has_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior (closure A)))) := by
  -- The set in question is open, hence it satisfies `P1`.
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  exact
    (Topology.isOpen_implies_P1
        (X := X)
        (A := interior (closure (interior (closure A))))) hOpen

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (interior (B : Set X))) := by
  -- First, use monotonicity of `interior` on the inclusion `A ⊆ B`.
  have hInt : (interior (A : Set X) : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  -- Next, apply `closure_mono` to obtain an inclusion between the closures.
  have hCl :
      closure (interior (A : Set X)) ⊆
        closure (interior (B : Set X)) := closure_mono hInt
  -- Finally, apply `interior_mono` once more to the previous inclusion.
  exact interior_mono hCl

theorem closure_interior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure (A : Set X) := by
  simpa [hA.interior_eq]

theorem interior_closure_interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) ⊆
      closure (interior (A : Set X)) := by
  simpa using
    (interior_subset :
      interior (closure (interior (A : Set X))) ⊆
        closure (interior (A : Set X)))

theorem interior_closure_eq_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior (A : Set X) := by
  simpa [hA.closure_eq]

theorem P3_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen (A : Set X) → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hOpenA hP3B
  -- An open set automatically satisfies `P3`.
  have hP3A : Topology.P3 A :=
    Topology.isOpen_implies_P3 (X := X) (A := A) hOpenA
  -- Combine the two sets using the existing union lemma for `P3`.
  exact Topology.P3_union (X := X) (A := A) (B := B) hP3A hP3B

theorem closure_interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X).Nonempty →
      (closure (interior (A : Set X))).Nonempty := by
  intro hP1 hA
  rcases hA with ⟨x, hxA⟩
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  exact ⟨x, hx_cl⟩

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  -- `A ⊆ B` implies `closure A ⊆ closure B`.
  have h_cl : closure (A : Set X) ⊆ closure (B : Set X) :=
    closure_mono hAB
  -- Applying `interior_mono` to the previous inclusion.
  have h_int : interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) :=
    interior_mono h_cl
  -- Taking closures preserves inclusions.
  exact closure_mono h_int

theorem interior_closure_interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  -- Idempotence of the pattern `interior ∘ closure ∘ interior`.
  have h₁ :=
    interior_closure_interior_idempotent (X := X) (A := A)
  calc
    interior (closure (interior (closure (interior (closure (interior A)))))) =
        interior (closure (interior (closure (interior A)))) := by
      simpa [h₁]
    _ = interior (closure (interior A)) := by
      simpa using h₁

theorem P2_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure A) := by
  exact
    (Topology.isOpen_implies_P2
        (X := X)
        (A := closure (A : Set X))) hOpen

theorem P1_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P1 (closure A) := by
  intro hOpen
  simpa [closure_closure] using
    (Topology.isOpen_implies_P1_closure
        (X := X) (A := closure (A : Set X))) hOpen

theorem P2_of_interior_closure_interior_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (closure (interior (A : Set X))) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have hx : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using hx

theorem interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ] using
    (interior_univ : interior (Set.univ : Set X) = (Set.univ : Set X))

theorem P3_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hP3_cl
  -- First upgrade `P3` to `P2` using the existing lemma.
  have hP2_cl : Topology.P2 (closure (A : Set X)) :=
    (Topology.P3_closure_implies_P2_closure (X := X) (A := A)) hP3_cl
  -- Then upgrade `P2` to `P1` using another existing lemma.
  exact (Topology.P2_closure_implies_P1_closure (X := X) (A := A)) hP2_cl

theorem interior_eq_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → interior (A : Set X) = A := by
  intro hP2
  have hOpen : IsOpen (A : Set X) :=
    ((Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP2
  simpa [hOpen.interior_eq] using rfl

theorem isOpen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → IsOpen (A : Set X) := by
  intro hP2
  simpa using
    ((Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed)).1 hP2

theorem P3_implies_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      (A : Set X) ⊆ interior (closure (interior (closure (A : Set X)))) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  -- Step 1: `A ⊆ interior (closure A)` by `P3`.
  have h₁ : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
  -- Step 2: `interior (closure A)` is contained in the target set.
  have h₂ :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) := by
    -- Basic inclusion into a closure.
    have hSub :
        (interior (closure (A : Set X)) : Set X) ⊆
          closure (interior (closure (A : Set X))) := subset_closure
    -- `interior (closure A)` is open.
    have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    -- Maximality of the interior of a set among open subsets.
    exact interior_maximal hSub hOpen
  -- Combine the two inclusions.
  exact h₁.trans h₂

theorem closure_interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A : Set X).Nonempty →
      (closure (interior (A : Set X))).Nonempty := by
  intro hP2 hA
  -- Upgrade `P2` to `P1`.
  have hP1 : Topology.P1 A := (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  -- Apply the existing non‐emptiness lemma for `P1`.
  exact (Topology.closure_interior_nonempty_of_P1 (X := X) (A := A)) hP1 hA

theorem closure_interior_inter_subset_intersection {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior ((A ∩ B) : Set X)) ⊆
      closure (interior (A : Set X)) ∩ closure (interior (B : Set X)) := by
  intro x hx
  -- `A ∩ B` is contained in `A`, hence so is its interior.
  have hSubA : interior ((A ∩ B) : Set X) ⊆ interior (A : Set X) := by
    have hAB_A : (A ∩ B : Set X) ⊆ (A : Set X) := by
      intro y hy
      exact hy.1
    exact interior_mono hAB_A
  -- Symmetrically for `B`.
  have hSubB : interior ((A ∩ B) : Set X) ⊆ interior (B : Set X) := by
    have hAB_B : (A ∩ B : Set X) ⊆ (B : Set X) := by
      intro y hy
      exact hy.2
    exact interior_mono hAB_B
  -- Transfer the inclusions to closures and assemble the result.
  have hxA : x ∈ closure (interior (A : Set X)) :=
    (closure_mono hSubA) hx
  have hxB : x ∈ closure (interior (B : Set X)) :=
    (closure_mono hSubB) hx
  exact And.intro hxA hxB

theorem P2_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  -- From `P2` and closedness, deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP2
  -- Every open set satisfies `P1`.
  exact (Topology.isOpen_implies_P1 (X := X) (A := A)) hOpen

theorem closure_inter_subset_inter_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  -- `A ∩ B` is contained in `A`, so the closure relation is preserved.
  have hSubA : (A ∩ B : Set X) ⊆ (A : Set X) := by
    intro y hy
    exact hy.1
  have hxA : x ∈ closure (A : Set X) := (closure_mono hSubA) hx
  -- Symmetrically for `B`.
  have hSubB : (A ∩ B : Set X) ⊆ (B : Set X) := by
    intro y hy
    exact hy.2
  have hxB : x ∈ closure (B : Set X) := (closure_mono hSubB) hx
  exact And.intro hxA hxB

theorem P2_implies_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hEquiv := Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hClosed
  exact (hEquiv).mp hP2

theorem closure_interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) ⊆
      closure (interior (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ closure (interior A)`.
      have hSub : closure (interior (A : Set X)) ⊆
          closure (interior (A ∪ B : Set X)) := by
        -- `interior A` is contained in `interior (A ∪ B)`.
        have hIntSub : interior (A : Set X) ⊆ interior (A ∪ B : Set X) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        -- Taking closures preserves inclusions.
        exact closure_mono hIntSub
      exact hSub hxA
  | inr hxB =>
      -- Handle the case `x ∈ closure (interior B)`.
      have hSub : closure (interior (B : Set X)) ⊆
          closure (interior (A ∪ B : Set X)) := by
        -- `interior B` is contained in `interior (A ∪ B)`.
        have hIntSub : interior (B : Set X) ⊆ interior (A ∪ B : Set X) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        -- Taking closures preserves inclusions.
        exact closure_mono hIntSub
      exact hSub hxB

theorem interior_closure_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆ closure (A : Set X) := by
  exact interior_subset

theorem P1_implies_closure_interior_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      closure (interior (A : Set X)) =
        closure (interior (closure (A : Set X))) := by
  intro hP1
  -- From `P1 A` we get `closure A = closure (interior A)`.
  have hEq1 : closure (A : Set X) = closure (interior (A : Set X)) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- `P1` is preserved under taking closures.
  have hP1_cl : Topology.P1 (closure (A : Set X)) :=
    (Topology.P1_implies_P1_closure (X := X) (A := A)) hP1
  -- Applying the same equivalence to `closure A`.
  have hEq2 : closure (A : Set X) =
      closure (interior (closure (A : Set X))) := by
    have h :=
      (Topology.P1_iff_closure_eq_closure_interior
          (X := X) (A := closure (A : Set X))).1 hP1_cl
    simpa [closure_closure] using h
  -- Combine the two equalities.
  have : closure (interior (A : Set X)) =
      closure (interior (closure (A : Set X))) := by
    calc
      closure (interior (A : Set X)) = closure (A : Set X) := by
        simpa using hEq1.symm
      _ = closure (interior (closure (A : Set X))) := hEq2
  simpa using this

theorem interior_closure_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆
      interior (closure (interior (closure (A : Set X)))) := by
  -- The set `interior (closure A)` is open.
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- And it is contained in `closure (interior (closure A))`.
  have hSub :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure (A : Set X))) :=
    subset_closure
  -- Apply the maximality property of `interior`.
  exact interior_maximal hSub hOpen

theorem P2_and_interior_eq_empty_implies_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → interior (A : Set X) = ∅ → A = (∅ : Set X) := by
  intro hP2 hIntEmpty
  dsimp [Topology.P2] at hP2
  -- Compute the target set: `interior (closure (interior A)) = ∅`.
  have hTarget : interior (closure (interior (A : Set X))) = (∅ : Set X) := by
    simpa [hIntEmpty, closure_empty, interior_empty]
  -- `P2` implies `A ⊆ interior (closure (interior A))`, hence `A ⊆ ∅`.
  have hSubset : (A : Set X) ⊆ (∅ : Set X) := by
    have h : (A : Set X) ⊆ interior (closure (interior (A : Set X))) := hP2
    simpa [hTarget] using h
  -- Conclude that `A = ∅`.
  exact Set.Subset.antisymm hSubset (Set.empty_subset _)

theorem interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (A : Set X)) : Set X) ⊆
      closure (interior (closure (A : Set X))) := by
  simpa using
    (subset_closure :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure (A : Set X))))

theorem closure_interior_closure_closure_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (closure (A : Set X)))) =
      closure (interior (closure (A : Set X))) := by
  simpa [closure_closure]

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  simpa [hDense] using
    (interior_univ : interior (Set.univ : Set X) = (Set.univ : Set X))

theorem interior_closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  -- First, translate the density assumption into an interior statement.
  have hIntUniv :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hDense] using
      (interior_univ : interior (Set.univ : Set X) = (Set.univ : Set X))
  -- Monotonicity of `closure` and `interior` yields the key inclusion.
  have hMono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    have hCl :
        closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    exact interior_mono hCl
  -- Hence `univ ⊆ interior (closure A)`.
  have hUnivSub :
      (Set.univ : Set X) ⊆ interior (closure (A : Set X)) := by
    simpa [hIntUniv] using hMono
  -- The reverse inclusion is trivial.
  have hSubUniv :
      interior (closure (A : Set X)) ⊆ (Set.univ : Set X) :=
    Set.subset_univ _
  exact Set.Subset.antisymm hSubUniv hUnivSub

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP1 hA
  -- Obtain a point in the interior of `A` using the existing lemma.
  rcases (Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA) with ⟨x, hxIntA⟩
  -- Monotonicity of `interior` yields the desired inclusion.
  have hMono : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
  exact ⟨x, hMono hxIntA⟩

theorem interior_closure_interior_closure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure (A : Set X)) := by
  -- Left‐to‐right inclusion.
  have h₁ :
      interior (closure (interior (closure (A : Set X)))) ⊆
        interior (closure (A : Set X)) := by
    -- Apply the existing monotonicity lemma to `A := closure A`.
    simpa [closure_closure] using
      (Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure (A : Set X)))
  -- Right‐to‐left inclusion.
  have h₂ :
      interior (closure (A : Set X)) ⊆
        interior (closure (interior (closure (A : Set X)))) :=
    Topology.interior_closure_subset_interior_closure_interior_closure
      (X := X) (A := A)
  exact Set.Subset.antisymm h₁ h₂

theorem interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A : Set X).Nonempty → (interior (A : Set X)).Nonempty := by
  intro hP2 hA
  -- First, upgrade `P2` to `P1`.
  have hP1 : Topology.P1 A :=
    (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  -- Then apply the existing non‐emptiness lemma for `P1`.
  exact (Topology.interior_nonempty_of_P1 (X := X) (A := A)) hP1 hA

theorem isOpen_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen (B : Set X)) :
    IsOpen ((interior (A : Set X)) ∪ B) := by
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  exact hA.union hB



theorem P1_implies_P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P2 (interior (A : Set X)) := by
  intro _
  -- `interior A` is open, hence it satisfies `P2`.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  exact
    (Topology.isOpen_implies_P2
        (X := X)
        (A := interior (A : Set X))) hOpen

theorem interior_inter_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆ interior (A : Set X) ∩ interior (B : Set X) := by
  intro x hx
  -- `A ∩ B` is contained in `A`, hence so is its interior.
  have hA : (A ∩ B : Set X) ⊆ (A : Set X) := by
    intro y hy
    exact hy.1
  -- Symmetrically, `A ∩ B` is contained in `B`.
  have hB : (A ∩ B : Set X) ⊆ (B : Set X) := by
    intro y hy
    exact hy.2
  -- Apply monotonicity of `interior` to transfer the membership.
  have hxA : x ∈ interior (A : Set X) := (interior_mono hA) hx
  have hxB : x ∈ interior (B : Set X) := (interior_mono hB) hx
  exact And.intro hxA hxB

theorem closure_interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
      closure (interior (A : Set X)) := by
  -- Reuse the basic idempotence lemma twice.
  have h₁ :
      closure (interior (closure (interior (A : Set X)))) =
        closure (interior (A : Set X)) :=
    Topology.closure_interior_closure_interior_idempotent (X := X) (A := A)
  calc
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
        closure (interior (closure (closure (interior (A : Set X))))) := by
          simpa [h₁]
    _ = closure (interior (closure (interior (A : Set X)))) := by
          simpa [closure_closure]
    _ = closure (interior (A : Set X)) := by
          simpa [h₁]

theorem P3_and_interior_closure_eq_empty_implies_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → interior (closure (A : Set X)) = ∅ → A = (∅ : Set X) := by
  intro hP3 hIntEmpty
  dsimp [Topology.P3] at hP3
  -- `P3` gives `A ⊆ interior (closure A)`, which is empty by hypothesis.
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    have : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    simpa [hIntEmpty] using this
  -- Conclude that `A = ∅`.
  exact Set.Subset.antisymm hSub (Set.empty_subset _)

theorem P2_iff_P3_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (A : Set X)) ↔ Topology.P3 (interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P2_iff_P3_of_isOpen
      (X := X) (A := interior (A : Set X)) hOpen)

theorem interior_subset_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ⊆ interior (A ∪ B : Set X) := by
  exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)

theorem sUnion_open_has_all_Ps {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → IsOpen (A : Set X)) :
    Topology.P1 (⋃₀ 𝒜) ∧ Topology.P2 (⋃₀ 𝒜) ∧ Topology.P3 (⋃₀ 𝒜) := by
  -- The union of an arbitrary family of open sets is open.
  have hOpen : IsOpen (⋃₀ 𝒜 : Set X) := isOpen_sUnion h𝒜
  -- Every open set satisfies `P1`, `P2`, and `P3`.
  simpa using
    (Topology.isOpen_has_all_Ps (X := X) (A := (⋃₀ 𝒜 : Set X)) hOpen)

theorem interior_subset_interior_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (B : Set X) ⊆ interior (A ∪ B : Set X) := by
  exact interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)

theorem P1_iff_P2_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P2 (interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P1_iff_P2_of_isOpen (X := X) (A := interior (A : Set X)) hOpen)

theorem union_interiors_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    (interior (A : Set X) ∪ interior (B : Set X)) ⊆
      interior (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior A`.
      have hMono : interior (A : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hMono hxA
  | inr hxB =>
      -- Handle the case `x ∈ interior B`.
      have hMono : interior (B : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hMono hxB

theorem open_union_has_all_Ps {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  exact Topology.isOpen_has_all_Ps (X := X) (A := (A ∪ B : Set X)) hOpen

theorem isOpen_union_interiors {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen ((interior (A : Set X)) ∪ interior (B : Set X)) := by
  -- Both `interior A` and `interior B` are open sets.
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hB : IsOpen (interior (B : Set X)) := isOpen_interior
  -- The union of two open sets is open.
  exact hA.union hB

theorem P3_mono {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → (A : Set X) ⊆ B →
      (A : Set X) ⊆ interior (closure (B : Set X)) := by
  intro hP3 hAB
  dsimp [Topology.P3] at hP3
  intro x hxA
  -- Via `P3`, `x` lies in `interior (closure A)`.
  have hx_intA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have h_cl : closure (A : Set X) ⊆ closure (B : Set X) := closure_mono hAB
  -- Applying monotonicity of `interior` to the previous inclusion.
  have h_mono : interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) :=
    interior_mono h_cl
  exact h_mono hx_intA

theorem P2_mono {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A →
    (A : Set X) ⊆ B →
    (A : Set X) ⊆ interior (closure (interior (B : Set X))) := by
  intro hP2 hAB
  dsimp [Topology.P2] at hP2
  intro x hxA
  have hxIntA : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  have hIntSub : interior (A : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  have hClSub :
      closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) :=
    closure_mono hIntSub
  have hMono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (interior (B : Set X))) :=
    interior_mono hClSub
  exact hMono hxIntA

theorem P1_mono {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → (A : Set X) ⊆ B →
      (A : Set X) ⊆ closure (interior (B : Set X)) := by
  intro hP1 hAB
  dsimp [Topology.P1] at hP1
  intro x hxA
  -- `P1` yields membership of `x` in `closure (interior A)`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- Monotonicity: `closure (interior A) ⊆ closure (interior B)`.
  have hSub : closure (interior (A : Set X)) ⊆
      closure (interior (B : Set X)) := by
    have hInt : interior (A : Set X) ⊆ interior (B : Set X) :=
      interior_mono hAB
    exact closure_mono hInt
  -- Conclude the desired membership.
  exact hSub hx_clA

theorem closure_union_interiors_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) =
      closure (interior (A : Set X) ∪ interior (B : Set X)) := by
  simpa using
    (closure_union (interior (A : Set X)) (interior (B : Set X))).symm

theorem P3_iff_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ (A : Set X) ⊆ interior (closure (A : Set X)) := by
  simpa [Topology.P3]

theorem P2_closure_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 (closure (A : Set X)) := by
  intro hP2_cl
  -- Using the closed–open equivalence for `P2`, deduce that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv := Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
    exact (hEquiv).1 hP2_cl
  -- Every open set satisfies `P3`.
  exact (Topology.isOpen_implies_P3 (X := X) (A := closure (A : Set X))) hOpen

theorem inter_open_has_all_Ps {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hP1 := Topology.P1_inter_of_open (X := X) (A := A) (B := B) hA hB
  have hP2 := Topology.P2_inter_of_open (X := X) (A := A) (B := B) hA hB
  have hP3 := Topology.P3_inter_of_open (X := X) (A := A) (B := B) hA hB
  exact And.intro hP1 (And.intro hP2 hP3)

theorem P1_iff_P3_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P3 (interior (A : Set X)) := by
  have h₁ :
      Topology.P1 (interior (A : Set X)) ↔
        Topology.P2 (interior (A : Set X)) :=
    (Topology.P1_iff_P2_of_interior (X := X) (A := A))
  have h₂ :
      Topology.P2 (interior (A : Set X)) ↔
        Topology.P3 (interior (A : Set X)) :=
    (Topology.P2_iff_P3_of_interior (X := X) (A := A))
  exact h₁.trans h₂

theorem P3_implies_P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (interior (A : Set X)) := by
  intro _
  simpa using (Topology.interior_has_P1 (X := X) (A := A))

theorem P1_and_interior_eq_empty_implies_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior (A : Set X) = ∅ → A = (∅ : Set X) := by
  intro hP1 hIntEmpty
  dsimp [Topology.P1] at hP1
  -- From `P1`, we know `A ⊆ closure (interior A)`.
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    have : (A : Set X) ⊆ closure (interior (A : Set X)) := hP1
    simpa [hIntEmpty, closure_empty] using this
  exact Set.Subset.antisymm hSub (Set.empty_subset _)

theorem closure_subset_closure_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
  -- The set `A` is (trivially) contained in `A ∪ B`.
  have hSub : (A : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  -- Taking closures preserves inclusions.
  exact closure_mono hSub



theorem closure_subset_closure_union_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
  -- `B` is contained in `A ∪ B`.
  have hSub : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  -- Taking closures preserves inclusions.
  exact closure_mono hSub

theorem interior_iInter_subset_iInter_interiors {X ι : Type*} [TopologicalSpace X]
    {F : ι → Set X} :
    interior (⋂ i, F i : Set X) ⊆ ⋂ i, interior (F i : Set X) := by
  intro x hx
  -- Show that `x` belongs to every `interior (F i)`.
  have h_mem : ∀ i, x ∈ interior (F i : Set X) := by
    intro i
    -- Use the inclusion `⋂ i, F i ⊆ F i`.
    have h_subset : (⋂ j, F j : Set X) ⊆ (F i : Set X) :=
      Set.iInter_subset (fun j ↦ F j) i
    exact (interior_mono h_subset) hx
  exact Set.mem_iInter.2 h_mem

theorem P2_iff_subset_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (A : Set X) ⊆ interior (closure (interior A)) := by
  rfl

theorem isOpen_closure_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      Topology.P1 (closure (A : Set X)) ∧
      Topology.P2 (closure (A : Set X)) ∧
      Topology.P3 (closure (A : Set X)) := by
  intro hOpen
  have hP1 := P1_closure_of_isOpen_closure (X := X) (A := A) hOpen
  have hP2 := P2_of_isOpen_closure (X := X) (A := A) hOpen
  have hP3 := P3_closure_of_isOpen_closure (X := X) (A := A) hOpen
  exact And.intro hP1 (And.intro hP2 hP3)

theorem P1_iff_P2_and_P3_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (A : Set X)) ↔
      (Topology.P2 (interior (A : Set X)) ∧ Topology.P3 (interior (A : Set X))) := by
  -- Pairwise equivalences for the open set `interior A`.
  have h₁ :
      Topology.P1 (interior (A : Set X)) ↔
        Topology.P2 (interior (A : Set X)) :=
    (Topology.P1_iff_P2_of_interior (X := X) (A := A))
  have h₂ :
      Topology.P2 (interior (A : Set X)) ↔
        Topology.P3 (interior (A : Set X)) :=
    (Topology.P2_iff_P3_of_interior (X := X) (A := A))
  -- Assemble the desired equivalence.
  constructor
  · intro hP1
    -- Convert `P1` into `P2`, then into `P3`.
    have hP2 : Topology.P2 (interior (A : Set X)) := (h₁).1 hP1
    have hP3 : Topology.P3 (interior (A : Set X)) := (h₂).1 hP2
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    -- Convert `P2` back into `P1` using the first equivalence.
    exact (h₁).2 hP2

theorem interior_inter_closures_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((closure (A : Set X)) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- `closure A ∩ closure B` is contained in each of the closures separately.
  have hSubA :
      (closure (A : Set X) ∩ closure (B : Set X)) ⊆ closure (A : Set X) := by
    intro y hy; exact hy.1
  have hSubB :
      (closure (A : Set X) ∩ closure (B : Set X)) ⊆ closure (B : Set X) := by
    intro y hy; exact hy.2
  -- Apply monotonicity of `interior` to both inclusions.
  have hxA : x ∈ interior (closure (A : Set X)) := (interior_mono hSubA) hx
  have hxB : x ∈ interior (closure (B : Set X)) := (interior_mono hSubB) hx
  exact And.intro hxA hxB

theorem P2_and_interior_closure_eq_empty_implies_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (A : Set X)) = ∅ → A = (∅ : Set X) := by
  intro hP2 hIntEmpty
  -- From `P2` we have the inclusion `A ⊆ interior (closure A)`.
  have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) :=
    (Topology.P2_implies_subset_interior_closure (X := X) (A := A)) hP2
  -- But `interior (closure A)` is empty by hypothesis, hence so is `A`.
  have hSubEmpty : (A : Set X) ⊆ (∅ : Set X) := by
    simpa [hIntEmpty] using hSub
  exact Set.Subset.antisymm hSubEmpty (Set.empty_subset _)

theorem interior_inter_has_all_Ps {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior ((A ∩ B) : Set X)) ∧
    Topology.P2 (interior ((A ∩ B) : Set X)) ∧
    Topology.P3 (interior ((A ∩ B) : Set X)) := by
  -- The set `interior (A ∩ B)` is open.
  have hOpen : IsOpen (interior ((A ∩ B) : Set X)) := isOpen_interior
  -- Every open set satisfies all three properties.
  exact
    Topology.isOpen_has_all_Ps
      (X := X) (A := interior (A ∩ B : Set X)) hOpen

theorem interior_inter_eq_self_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = (A ∩ B : Set X) := by
  have hOpen : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  simpa [hOpen.interior_eq]

theorem iUnion_open_has_all_Ps {X ι : Type*} [TopologicalSpace X] {F : ι → Set X}
    (hF : ∀ i, IsOpen (F i : Set X)) :
    Topology.P1 (⋃ i, F i) ∧ Topology.P2 (⋃ i, F i) ∧ Topology.P3 (⋃ i, F i) := by
  have hOpen : IsOpen (⋃ i, F i : Set X) := isOpen_iUnion (fun i ↦ hF i)
  exact Topology.isOpen_has_all_Ps (X := X) (A := (⋃ i, F i : Set X)) hOpen

theorem compl_closed_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen ((Aᶜ) : Set X) := hA.isOpen_compl
  exact Topology.isOpen_has_all_Ps (X := X) (A := (Aᶜ : Set X)) hOpen

theorem interior_union_eq_self_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = (A ∪ B : Set X) := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa [hOpen.interior_eq]

theorem closure_inter_interior_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (A : Set X) ∩ interior (A : Set X)) = interior (A : Set X) := by
  ext x
  constructor
  · intro h
    exact h.2
  · intro hxInt
    have hxCl : x ∈ closure (A : Set X) := by
      have hxA : x ∈ (A : Set X) := interior_subset hxInt
      exact subset_closure hxA
    exact And.intro hxCl hxInt

theorem interior_eq_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P3 A → interior (A : Set X) = A := by
  intro hP3
  -- From `P3` and the fact that `A` is closed, deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP3
  -- The interior of an open set coincides with the set itself.
  simpa [hOpen.interior_eq]

theorem P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Equivalences already established for open sets.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Assemble the desired equivalence.
  constructor
  · intro hP1
    have hP2 : Topology.P2 A := h₁.mp hP1
    have hP3 : Topology.P3 A := h₂.mp hP2
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    exact h₁.mpr hP2

theorem P3_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔
      ∃ U : Set X, IsOpen U ∧ (A : Set X) ⊆ U ∧ U ⊆ closure (A : Set X) := by
  dsimp [Topology.P3]
  constructor
  · intro hP3
    refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, interior_subset⟩
    exact hP3
  · rintro ⟨U, hU_open, hA_sub_U, hU_sub_cl⟩
    -- Any open set contained in `closure A` is contained in its interior.
    have hU_sub_int : (U : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_maximal hU_sub_cl hU_open
    -- Assemble the desired inclusion.
    intro x hxA
    exact hU_sub_int (hA_sub_U hxA)

theorem P1_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X) ⊆ closure (interior A) := by
  intro hP1
  simpa [Topology.P1] using hP1

theorem P1_iff_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔
      ∃ U : Set X, IsOpen U ∧ (U ⊆ A) ∧ (A : Set X) ⊆ closure U := by
  constructor
  · intro hP1
    refine
      ⟨interior (A : Set X), isOpen_interior, interior_subset, ?_⟩
    simpa [Topology.P1] using hP1
  · rintro ⟨U, hU_open, hU_sub_A, hA_sub_clU⟩
    dsimp [Topology.P1]
    have hU_sub_intA : (U : Set X) ⊆ interior (A : Set X) :=
      interior_maximal hU_sub_A hU_open
    have h_clU_sub :
        closure (U : Set X) ⊆ closure (interior (A : Set X)) :=
      closure_mono hU_sub_intA
    intro x hxA
    have hx_clU : x ∈ closure (U : Set X) := hA_sub_clU hxA
    exact h_clU_sub hx_clU

theorem closure_interior_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (interior (A : Set X)) =
        closure (interior (closure (A : Set X))) := by
  intro hP2
  -- Upgrade `P2` to `P1`.
  have hP1 : Topology.P1 A :=
    (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  -- Apply the equality obtained from `P1`.
  exact
    (Topology.P1_implies_closure_interior_eq_closure_interior_closure
      (X := X) (A := A)) hP1

theorem interior_closure_union_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∪ B) : Set X)) =
      interior (closure (A : Set X) ∪ closure (B : Set X)) := by
  simpa [closure_union]

theorem interior_closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A : Set X).Nonempty →
      (interior (closure (interior (A : Set X)))).Nonempty := by
  intro hP2 hA
  rcases hA with ⟨x, hxA⟩
  have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  exact ⟨x, hx⟩

theorem closure_interior_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- The interior of `A` is contained in `A`.
  have hInt : interior (A : Set X) ⊆ (A : Set X) := interior_subset
  -- Taking closures preserves inclusions.
  have hCl : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono hInt
  -- Since `A` is closed, its closure equals itself.
  simpa [hA.closure_eq] using hCl

theorem P3_implies_P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P2 (interior (A : Set X)) := by
  intro _
  -- `interior A` is open, so it satisfies `P2`.
  exact
    (Topology.isOpen_implies_P2 (X := X)
      (A := interior (A : Set X))) isOpen_interior

theorem interior_closure_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    (interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) ∪
        interior (closure (C : Set X))) ⊆
      interior (closure (A ∪ B ∪ C : Set X)) := by
  intro x hx
  -- Split according to the part of the three‐way union that contains `x`.
  cases hx with
  | inl hAB =>
      -- `x` lies in the union of the first two interiors.
      have h₁ :
          interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) ⊆
            interior (closure (A ∪ B : Set X)) :=
        interior_closure_union_subset (X := X) (A := A) (B := B)
      have hxAB : x ∈ interior (closure (A ∪ B : Set X)) := h₁ hAB
      -- Enlarge `A ∪ B` to `A ∪ B ∪ C`.
      have hMono :
          interior (closure (A ∪ B : Set X)) ⊆
            interior (closure (A ∪ B ∪ C : Set X)) := by
        have hCl :
            closure (A ∪ B : Set X) ⊆ closure (A ∪ B ∪ C : Set X) := by
          have hSub : (A ∪ B : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            cases hy with
            | inl hyA => exact Or.inl (Or.inl hyA)
            | inr hyB => exact Or.inl (Or.inr hyB)
          exact closure_mono hSub
        exact interior_mono hCl
      exact hMono hxAB
  | inr hC =>
      -- `x` lies in the third interior.
      have hCl :
          closure (C : Set X) ⊆ closure (A ∪ B ∪ C : Set X) := by
        have hSub : (C : Set X) ⊆ A ∪ B ∪ C := by
          intro y hy
          exact Or.inr hy
        exact closure_mono hSub
      have hMono :
          interior (closure (C : Set X)) ⊆
            interior (closure (A ∪ B ∪ C : Set X)) :=
        interior_mono hCl
      exact hMono hC



theorem closure_interior_eq_empty_iff_interior_eq_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔
      interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro h
    have hSub : interior (A : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure (interior (A : Set X)) := subset_closure hx
      simpa [h] using this
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro h
    simpa [h, closure_empty]

theorem P1_iff_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ (A : Set X) ⊆ closure (interior A) := by
  rfl

theorem P2_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔
      ∃ U : Set X, IsOpen U ∧ (A : Set X) ⊆ U ∧
        U ⊆ closure (interior (A : Set X)) := by
  dsimp [Topology.P2]
  constructor
  · intro hP2
    refine
      ⟨interior (closure (interior (A : Set X))), isOpen_interior, hP2, ?_⟩
    exact interior_subset
  · rintro ⟨U, hU_open, hA_sub_U, hU_sub_cl⟩
    have hU_sub_int :
        (U : Set X) ⊆ interior (closure (interior (A : Set X))) :=
      interior_maximal hU_sub_cl hU_open
    exact hA_sub_U.trans hU_sub_int

theorem interior_closure_eq_self_of_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure (A : Set X)) →
      interior (closure (A : Set X)) = closure (A : Set X) := by
  intro hOpen
  simpa using hOpen.interior_eq

theorem closure_inter_eq_self_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = (A ∩ B : Set X) := by
  simpa using (hA.inter hB).closure_eq

theorem closure_interior_closure_eq_self_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  intro hOpen
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) := by
    simpa using hOpen.interior_eq
  calc
    closure (interior (closure (A : Set X))) =
        closure (closure (A : Set X)) := by
      simpa [hInt]
    _ = closure (A : Set X) := by
      simpa [closure_closure]

theorem P2_closure_interior_iff_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  -- `closure (interior A)` is always a closed set.
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Apply the closed–open characterization of `P2`.
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X)
      (A := closure (interior (A : Set X)))
      hClosed)

theorem closure_interior_eq_self_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- Since `A` is open, `closure (interior A) = closure A`.
  have h₁ : closure (interior (A : Set X)) = closure (A : Set X) :=
    closure_interior_eq_closure_of_isOpen (X := X) (A := A) hOpen
  -- Because `A` is closed, `closure A = A`.
  have h₂ : closure (A : Set X) = A := hClosed.closure_eq
  -- Combine the two equalities.
  simpa [h₂] using h₁

theorem isOpen_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    IsOpen (A ∪ interior (B : Set X)) := by
  have hIntB : IsOpen (interior (B : Set X)) := isOpen_interior
  exact hA.union hIntB

theorem closure_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X)).Nonempty ↔ (A : Set X).Nonempty := by
  classical
  constructor
  · intro hCl
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · -- If `A` is empty, then its closure is also empty, contradicting `hCl`.
      have hA_eq : (A : Set X) = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
      have hCl_eq : closure (A : Set X) = (∅ : Set X) := by
        simpa [hA_eq] using closure_empty
      have hFalse : False := by
        -- `hCl` yields a point in `closure A`, hence (by `hCl_eq`) in `∅`.
        have h' : (∅ : Set X).Nonempty := by
          simpa [hCl_eq] using hCl
        rcases h' with ⟨x, hx⟩
        cases hx
      exact hFalse.elim
  · intro hA
    rcases hA with ⟨x, hxA⟩
    exact ⟨x, subset_closure hxA⟩



theorem closure_interior_nonempty_iff_interior_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (closure (interior (A : Set X))).Nonempty ↔
      (interior (A : Set X)).Nonempty := by
  classical
  -- Translate the previously proved emptiness equivalence into a non‐emptiness equivalence.
  have hEmpty :
      closure (interior (A : Set X)) = (∅ : Set X) ↔
        interior (A : Set X) = (∅ : Set X) :=
    Topology.closure_interior_eq_empty_iff_interior_eq_empty
      (X := X) (A := A)
  simpa [Set.nonempty_iff_ne_empty] using not_congr hEmpty

theorem P2_closure_interior_closure_iff_isOpen_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure (A : Set X)))) ↔
      IsOpen (closure (interior (closure (A : Set X)))) := by
  have hClosed : IsClosed (closure (interior (closure (A : Set X)))) :=
    isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X)
      (A := closure (interior (closure (A : Set X))))
      hClosed)

theorem interior_closure_interior_inter_subset_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior ((A ∩ B) : Set X))) ⊆
      interior (closure (interior (A : Set X))) ∩
        interior (closure (interior (B : Set X))) := by
  -- First, relate the closures of the interiors.
  have h₁ :
      closure (interior ((A ∩ B) : Set X)) ⊆
        closure (interior (A : Set X)) ∩ closure (interior (B : Set X)) :=
    Topology.closure_interior_inter_subset_intersection
      (X := X) (A := A) (B := B)
  -- Apply `interior_mono` to obtain an inclusion between the interiors.
  have h₂ :
      interior (closure (interior ((A ∩ B) : Set X))) ⊆
        interior
          (closure (interior (A : Set X)) ∩ closure (interior (B : Set X))) :=
    interior_mono h₁
  -- Distribute `interior` over the intersection on the right‐hand side.
  have h₃ :
      interior
          (closure (interior (A : Set X)) ∩ closure (interior (B : Set X))) ⊆
        interior (closure (interior (A : Set X))) ∩
          interior (closure (interior (B : Set X))) := by
    simpa using
      (Topology.interior_inter_subset_interiors
        (X := X)
        (A := closure (interior (A : Set X)))
        (B := closure (interior (B : Set X))))
  exact h₂.trans h₃

theorem interior_inter_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    interior ((A ∩ B) : Set X) = (A : Set X) ∩ interior (B : Set X) := by
  -- First, show the left‐to‐right inclusion.
  have h₁ :
      (interior ((A ∩ B) : Set X) : Set X) ⊆
        (A : Set X) ∩ interior (B : Set X) := by
    intro x hx
    -- Membership in `interior (A ∩ B)` yields membership in `A ∩ B`.
    have hxAB : x ∈ (A : Set X) ∩ B := interior_subset hx
    -- Monotonicity: `interior (A ∩ B) ⊆ interior B`.
    have hxIntB : x ∈ interior (B : Set X) := by
      have hSub : ((A ∩ B) : Set X) ⊆ (B : Set X) := by
        intro y hy; exact hy.2
      exact (interior_mono hSub) hx
    exact And.intro hxAB.1 hxIntB
  -- Next, show the right‐to‐left inclusion.
  have h₂ :
      ((A : Set X) ∩ interior (B : Set X) : Set X) ⊆
        interior ((A ∩ B) : Set X) := by
    -- The set on the left is open, being the intersection of two open sets.
    have hOpen :
        IsOpen (((A : Set X) ∩ interior (B : Set X)) : Set X) :=
      hA.inter isOpen_interior
    -- It is contained in `A ∩ B`.
    have hSub :
        ((A : Set X) ∩ interior (B : Set X) : Set X) ⊆ (A : Set X) ∩ B := by
      intro y hy; exact And.intro hy.1 (interior_subset hy.2)
    -- Apply the maximality property of the interior.
    exact interior_maximal hSub hOpen
  exact Set.Subset.antisymm h₁ h₂

theorem P2_iff_P3_of_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) ↔
      Topology.P3 (closure (interior (A : Set X))) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  have h₁ :
      Topology.P2 (closure (interior (A : Set X))) ↔
        IsOpen (closure (interior (A : Set X))) :=
    Topology.P2_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (A : Set X))) hClosed
  have h₂ :
      Topology.P3 (closure (interior (A : Set X))) ↔
        IsOpen (closure (interior (A : Set X))) :=
    Topology.P3_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (A : Set X))) hClosed
  exact h₁.trans h₂.symm

theorem nonempty_of_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro hInt
  -- From a point in `interior (closure A)` we obtain a point in `closure A`.
  have hCl : (closure (A : Set X)).Nonempty := by
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩
  -- Use the equivalence between non-emptiness of `closure A` and of `A`.
  exact ((Topology.closure_nonempty_iff (X := X) (A := A)).1) hCl

theorem P1_and_closure_interior_eq_empty_implies_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      closure (interior (A : Set X)) = (∅ : Set X) →
      A = (∅ : Set X) := by
  intro hP1 hClEmpty
  -- From `P1`, we have `A ⊆ closure (interior A)`.
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : x ∈ closure (interior (A : Set X)) := hP1 hxA
    simpa [hClEmpty] using this
  exact Set.Subset.antisymm hSub (Set.empty_subset _)

theorem interior_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = interior (A : Set X) ∩ B := by
  -- Left-to-right inclusion.
  have h₁ :
      (interior ((A ∩ B) : Set X) : Set X) ⊆ interior (A : Set X) ∩ B := by
    intro x hx
    -- Membership in `interior (A ∩ B)` implies membership in `A ∩ B`.
    have hxAB : x ∈ (A : Set X) ∩ B := interior_subset hx
    -- Monotonicity of `interior` for the inclusion `A ∩ B ⊆ A`.
    have hxIntA : x ∈ interior (A : Set X) := by
      have hSub : (A ∩ B : Set X) ⊆ (A : Set X) := by
        intro y hy; exact hy.1
      exact (interior_mono hSub) hx
    exact And.intro hxIntA hxAB.2
  -- Right-to-left inclusion.
  have h₂ :
      (interior (A : Set X) ∩ B : Set X) ⊆ interior ((A ∩ B) : Set X) := by
    -- The set on the left is open as the intersection of two open sets.
    have hOpen : IsOpen ((interior (A : Set X)) ∩ B : Set X) :=
      (isOpen_interior).inter hB
    -- It is contained in `A ∩ B`.
    have hSub :
        ((interior (A : Set X)) ∩ B : Set X) ⊆ (A : Set X) ∩ B := by
      intro y hy; exact And.intro (interior_subset hy.1) hy.2
    -- Use the maximality property of `interior`.
    exact interior_maximal hSub hOpen
  exact Set.Subset.antisymm h₁ h₂

theorem nonempty_of_closure_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro hClInt
  -- First, obtain a point in `interior A` using the previously proven equivalence.
  have hInt :
      (interior (A : Set X)).Nonempty :=
    ((Topology.closure_interior_nonempty_iff_interior_nonempty
        (X := X) (A := A))).1 hClInt
  -- Since `interior A ⊆ A`, this point also lies in `A`.
  rcases hInt with ⟨x, hxInt⟩
  exact ⟨x, interior_subset hxInt⟩

theorem P2_implies_P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 (interior (A : Set X)) := by
  intro hP2
  -- Step 1: `P2` propagates from `A` to its interior.
  have hP2_int : Topology.P2 (interior (A : Set X)) :=
    (Topology.P2_implies_P2_interior (X := X) (A := A)) hP2
  -- Step 2: For the open set `interior A`, `P2` and `P3` are equivalent.
  have hEquiv :=
    (Topology.P2_iff_P3_of_interior (X := X) (A := A))
  -- Step 3: Convert `P2` into `P3` via the equivalence.
  exact (hEquiv).1 hP2_int

theorem P2_iff_P3_of_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of an open set is closed.
  have hClosed : IsClosed ((Aᶜ) : Set X) := hA.isClosed_compl
  -- Apply the existing equivalence for closed sets.
  simpa using
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := (Aᶜ)) hClosed)

theorem P1_iff_P3_of_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (A : Set X))) ↔
      Topology.P3 (interior (closure (A : Set X))) := by
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  exact
    Topology.P1_iff_P3_of_isOpen
      (X := X) (A := interior (closure (A : Set X))) hOpen

theorem interior_closure_inter_left_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ interior (B : Set X)) : Set X)) ⊆
      interior (closure (A : Set X)) := by
  -- `A ∩ interior B` is contained in `A`.
  have hSub : (A ∩ interior (B : Set X) : Set X) ⊆ (A : Set X) := by
    intro x hx
    exact hx.1
  -- Apply monotonicity of `closure` and then of `interior`.
  exact interior_mono (closure_mono hSub)

theorem closure_subset_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      closure (A : Set X) ⊆
        closure (interior (closure (A : Set X))) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  exact closure_mono hP3

theorem union_closures_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hxA =>
      exact
        (Topology.closure_subset_closure_union_left
          (X := X) (A := A) (B := B)) hxA
  | inr hxB =>
      exact
        (Topology.closure_subset_closure_union_right
          (X := X) (A := A) (B := B)) hxB



theorem interior_closure_inter_right_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((interior (A : Set X) ∩ B) : Set X)) ⊆
      interior (closure (B : Set X)) := by
  -- The set `interior A ∩ B` is contained in `B`.
  have hSub : (interior (A : Set X) ∩ B : Set X) ⊆ (B : Set X) := by
    intro x hx
    exact hx.2
  -- Monotonicity of `closure` and then of `interior` yields the result.
  exact interior_mono (closure_mono hSub)

theorem closure_iInter_subset_iInter_closures {X ι : Type*} [TopologicalSpace X]
    {F : ι → Set X} :
    closure (⋂ i, F i : Set X) ⊆ ⋂ i, closure (F i : Set X) := by
  intro x hx
  apply Set.mem_iInter.2
  intro i
  -- Since `⋂ i, F i ⊆ F i`, taking closures preserves the inclusion.
  have hSub : closure (⋂ j, F j : Set X) ⊆ closure (F i : Set X) := by
    have hSubset : (⋂ j, F j : Set X) ⊆ (F i : Set X) :=
      Set.iInter_subset (fun j ↦ F j) i
    exact closure_mono hSubset
  exact hSub hx

theorem iUnion_interiors_subset_interior_iUnion
    {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (⋃ i, interior (F i : Set X)) ⊆ interior (⋃ i, F i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxInt⟩
  have h_mono :
      interior (F i : Set X) ⊆ interior (⋃ j, F j : Set X) :=
    interior_mono (Set.subset_iUnion _ _)
  exact h_mono hxInt

theorem interior_subset_closure_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X) : Set X) ⊆ closure (A : Set X) := by
  intro x hxInt
  have hxA : x ∈ (A : Set X) := interior_subset hxInt
  exact subset_closure hxA

theorem interior_inter_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((interior (A : Set X) ∩ interior (B : Set X)) : Set X) =
      interior (A : Set X) ∩ interior (B : Set X) := by
  have hOpenA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hOpenB : IsOpen (interior (B : Set X)) := isOpen_interior
  simpa using
    interior_inter_eq_self_of_open
      (X := X)
      (A := interior (A : Set X))
      (B := interior (B : Set X))
      hOpenA
      hOpenB

theorem closure_interior_eq_self_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P3 A → closure (interior (A : Set X)) = A := by
  intro hP3
  -- From `P3` and closedness, deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP3
  -- A clopen set satisfies `closure (interior A) = A`.
  exact
    Topology.closure_interior_eq_self_of_clopen
      (X := X) (A := A) hOpen hClosed

theorem closure_inter_interior_subset_inter_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A : Set X) ∩ interior (B : Set X)) ⊆
      closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  -- From `A ∩ interior B ⊆ A`, deduce membership in `closure A`.
  have hSubA :
      ((A : Set X) ∩ interior (B : Set X)) ⊆ (A : Set X) := by
    intro y hy; exact hy.1
  have hxA : x ∈ closure (A : Set X) := (closure_mono hSubA) hx
  -- From `A ∩ interior B ⊆ B`, deduce membership in `closure B`.
  have hSubB :
      ((A : Set X) ∩ interior (B : Set X)) ⊆ (B : Set X) := by
    intro y hy; exact
      (interior_subset : interior (B : Set X) ⊆ (B : Set X)) hy.2
  have hxB : x ∈ closure (B : Set X) := (closure_mono hSubB) hx
  exact And.intro hxA hxB

theorem union_interiors_eq_interior_union_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A : Set X) ∪ interior (B : Set X) = interior (A ∪ B : Set X) := by
  calc
    interior (A : Set X) ∪ interior (B : Set X)
        = (A : Set X) ∪ (B : Set X) := by
          simp [hA.interior_eq, hB.interior_eq]
    _ = interior (A ∪ B : Set X) := by
          have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
          simpa [hOpen.interior_eq]

theorem P1_union_of_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 A → (B : Set X) ⊆ closure (interior A) → Topology.P1 (A ∪ B) := by
  intro hP1 hB
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  -- `closure (interior A)` is contained in the target set via monotonicity.
  have hMono :
      closure (interior (A : Set X)) ⊆
        closure (interior (A ∪ B : Set X)) := by
    apply closure_mono
    exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Dispatch the two union cases.
  cases hx with
  | inl hxA =>
      have : x ∈ closure (interior (A : Set X)) := hP1 hxA
      exact hMono this
  | inr hxB =>
      have : x ∈ closure (interior (A : Set X)) := hB hxB
      exact hMono this

theorem closure_union_interiors_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior (B : Set X)) ⊆
      closure (interior (A ∪ B : Set X)) := by
  -- `interior A ∪ interior B` is contained in `interior (A ∪ B)` by a previously proved lemma.
  have hSub :
      ((interior (A : Set X)) ∪ interior (B : Set X) : Set X) ⊆
        interior (A ∪ B : Set X) :=
    union_interiors_subset_interior_union (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono hSub

theorem closure_subset_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (A : Set X) ⊆ closure (interior A) := by
  intro hP2
  -- First, derive an inclusion involving a more complicated target set.
  have hSub :=
    Topology.P2_implies_closure_subset_closure_interior_closure_interior
      (X := X) (A := A) hP2
  -- Simplify the target set using the idempotence lemma.
  have hId :
      closure (interior (closure (interior (A : Set X)))) =
        closure (interior (A : Set X)) :=
    Topology.closure_interior_closure_interior_idempotent (X := X) (A := A)
  -- Rewriting with `hId` yields the desired inclusion.
  simpa [hId] using hSub



theorem closure_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (∅ : Set X) ↔ (A : Set X) = ∅ := by
  constructor
  · intro h
    -- Since `A ⊆ closure A`, the hypothesis forces `A` to be empty.
    have hSub : (A : Set X) ⊆ (∅ : Set X) := by
      have : (A : Set X) ⊆ closure (A : Set X) := subset_closure
      simpa [h] using this
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro h
    -- Replace `A` with `∅` in the left‐hand side and use `closure_empty`.
    simpa [h, closure_empty]

theorem P2_union_interior_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 (A ∪ interior (B : Set X)) := by
  intro hP2A
  have hOpenInt : IsOpen (interior (B : Set X)) := isOpen_interior
  exact
    (Topology.P2_union_right_of_open
      (X := X) (A := A) (B := interior (B : Set X))) hP2A hOpenInt

theorem interior_nonempty_implies_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hIntA
  rcases hIntA with ⟨x, hxIntA⟩
  -- `interior A` is contained in `interior (closure A)` by monotonicity.
  have hMono :
      (interior (A : Set X) : Set X) ⊆
        interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
  exact ⟨x, hMono hxIntA⟩

theorem P1_iUnion_closure {X ι : Type*} [TopologicalSpace X] {F : ι → Set X}
    (hF : ∀ i, Topology.P1 (F i)) :
    Topology.P1 (⋃ i, closure (F i : Set X)) := by
  -- Each `closure (F i)` inherits `P1` from `F i`.
  have hF_cl : ∀ i, Topology.P1 (closure (F i : Set X)) := by
    intro i
    exact Topology.P1_implies_P1_closure (X := X) (A := F i) (hF i)
  -- Apply the existing `iUnion` lemma to the family of closures.
  have h :=
    Topology.P1_iUnion (X := X)
      (F := fun i ↦ closure (F i : Set X)) hF_cl
  simpa using h

theorem closure_iInter_interiors_subset_iInter_closure_interiors
    {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    closure (⋂ i, interior (F i : Set X)) ⊆ ⋂ i, closure (interior (F i : Set X)) := by
  intro x hx
  -- For each `i`, we show `x ∈ closure (interior (F i))`.
  have h : ∀ i, x ∈ closure (interior (F i : Set X)) := by
    intro i
    -- The set `⋂ i, interior (F i)` is contained in `interior (F i)`.
    have hSubset :
        (⋂ j, interior (F j : Set X)) ⊆ interior (F i : Set X) :=
      Set.iInter_subset _ _
    -- Taking closures preserves inclusions.
    have hCl :
        closure (⋂ j, interior (F j : Set X)) ⊆
          closure (interior (F i : Set X)) :=
      closure_mono hSubset
    exact hCl hx
  -- Assemble the memberships into an element of the intersection.
  exact Set.mem_iInter.mpr h

theorem isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P3 A → IsOpen (A : Set X) := by
  intro hP3
  have hEquiv :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed
  exact (hEquiv).1 hP3

theorem P2_iff_P1_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Existing equivalences for open sets.
  have h₁ := Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ := Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Forward implication: `P2` gives both `P1` and `P3`.
  constructor
  · intro hP2
    have hP1 : Topology.P1 A := (h₁).mpr hP2
    have hP3 : Topology.P3 A := (h₂).mp hP2
    exact And.intro hP1 hP3
  -- Reverse implication: from `P1` (and hence `P2`) obtain `P2`.
  · rintro ⟨hP1, _⟩
    exact (h₁).mp hP1

theorem P3_union_interior_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 (A ∪ interior (B : Set X)) := by
  intro hP3A
  have hOpenInt : IsOpen (interior (B : Set X)) := isOpen_interior
  exact
    Topology.P3_union_right_of_open
      (X := X) (A := A) (B := interior (B : Set X)) hP3A hOpenInt

theorem closures_union_three_eq_closure_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ∪ closure (C : Set X) =
      closure (A ∪ B ∪ C : Set X) := by
  calc
    (closure (A : Set X)) ∪ closure (B : Set X) ∪ closure (C : Set X)
        = (closure (A : Set X) ∪ closure (B : Set X)) ∪ closure (C : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B : Set X) ∪ closure (C : Set X) := by
          simpa [closure_union]
    _ = closure ((A ∪ B) ∪ C : Set X) := by
          simpa [closure_union]
    _ = closure (A ∪ B ∪ C : Set X) := by
          simpa [Set.union_assoc]

theorem P2_iff_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) ↔ Topology.P3 (∅ : Set X) := by
  have hP2 : Topology.P2 (∅ : Set X) := Topology.P2_empty (X := X)
  have hP3 : Topology.P3 (∅ : Set X) := Topology.P3_empty (X := X)
  constructor
  · intro _; exact hP3
  · intro _; exact hP2

theorem P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Equivalences already established for open sets.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Assemble the desired equivalence.
  constructor
  · intro hP3
    -- Convert `P3` into `P2`, then into `P1`.
    have hP2 : Topology.P2 A := (h₂).mpr hP3
    have hP1 : Topology.P1 A := (h₁).mpr hP2
    exact And.intro hP1 hP2
  · rintro ⟨_, hP2⟩
    -- Convert `P2` back into `P3` using the second equivalence.
    exact (h₂).mp hP2

theorem P2_of_isOpen_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior (A : Set X))) →
      Topology.P2 (closure (interior (A : Set X))) := by
  intro hOpen
  have hEquiv :=
    (Topology.P2_closure_interior_iff_isOpen_closure_interior
      (X := X) (A := A))
  exact (hEquiv).2 hOpen

theorem isOpen_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (interior (closure (interior (A : Set X)))) := by
  exact isOpen_interior

theorem closure_nonempty_of_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X).Nonempty → (closure (A : Set X)).Nonempty := by
  intro hA
  rcases hA with ⟨x, hx⟩
  exact ⟨x, subset_closure hx⟩

theorem interior_union_three_eq_self_of_open
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) :
    interior (A ∪ B ∪ C : Set X) = (A ∪ B ∪ C : Set X) := by
  -- The triple union of open sets is open.
  have hOpen : IsOpen ((A ∪ B ∪ C) : Set X) := (hA.union hB).union hC
  simpa using hOpen.interior_eq

theorem P1_iff_P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) := by
  -- Both properties hold for the empty set, yielding the equivalence.
  have hP1 : Topology.P1 (∅ : Set X) := Topology.P1_empty (X := X)
  have hP2 : Topology.P2 (∅ : Set X) := Topology.P2_empty (X := X)
  exact ⟨fun _ => hP2, fun _ => hP1⟩

theorem P1_iff_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔ Topology.P3 (∅ : Set X) := by
  have h₁ := (Topology.P1_iff_P2_empty (X := X))
  have h₂ := (Topology.P2_iff_P3_empty (X := X))
  exact h₁.trans h₂

theorem P2_union_interior_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 B → Topology.P2 (interior (A : Set X) ∪ B) := by
  intro hP2B
  have hOpenInt : IsOpen (interior (A : Set X)) := isOpen_interior
  exact
    Topology.P2_union_left_of_open
      (X := X) (A := interior (A : Set X)) (B := B) hOpenInt hP2B

theorem closure_union_interior_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∪ interior (B : Set X)) : Set X) ⊆
      closure (A ∪ B : Set X) := by
  -- First, note that `A ∪ interior B ⊆ A ∪ B`.
  have hSub : ((A ∪ interior (B : Set X)) : Set X) ⊆ A ∪ B := by
    intro x hx
    cases hx with
    | inl hxA => exact Or.inl hxA
    | inr hxIntB =>
        exact Or.inr (interior_subset hxIntB)
  -- Taking closures preserves inclusions.
  exact closure_mono hSub

theorem P3_iff_forall_open_neighborhood {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔
      ∀ x ∈ (A : Set X), ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (A : Set X) := by
  -- Forward implication: construct a single open set that works for every point.
  constructor
  · intro hP3 x hxA
    refine
      ⟨interior (closure (A : Set X)), isOpen_interior, ?_, interior_subset⟩
    exact hP3 hxA
  -- Reverse implication: each point has an appropriate neighbourhood, hence lies in the interior.
  · intro h
    dsimp [Topology.P3]
    intro x hxA
    rcases h x hxA with ⟨U, hU_open, hxU, hU_sub⟩
    -- Any open set contained in `closure A` is contained in its interior.
    have hU_in_int :
        (U : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_maximal hU_sub hU_open
    exact hU_in_int hxU

theorem interior_union_has_all_Ps {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior ((A ∪ B) : Set X)) ∧
      Topology.P2 (interior ((A ∪ B) : Set X)) ∧
        Topology.P3 (interior ((A ∪ B) : Set X)) := by
  have hOpen : IsOpen (interior ((A ∪ B) : Set X)) := isOpen_interior
  exact
    Topology.isOpen_has_all_Ps
      (X := X) (A := interior ((A ∪ B) : Set X)) hOpen

theorem interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- Since `interior (closure A) = univ`, the inclusion
    -- `interior (closure A) ⊆ closure A` yields `univ ⊆ closure A`.
    have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      simpa [hInt] using
        (interior_subset :
          interior (closure (A : Set X)) ⊆ closure (A : Set X))
    -- Combine with the trivial inclusion `closure A ⊆ univ`.
    exact Set.Subset.antisymm (Set.subset_univ _) hSub
  · intro hCl
    -- If `closure A = univ`, its interior is also `univ`.
    simpa [hCl] using
      (interior_univ : interior (Set.univ : Set X) = (Set.univ : Set X))

theorem isOpen_closure_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP3_cl
  have hEquiv := Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  exact (hEquiv).1 hP3_cl

theorem union_interiors_has_all_Ps {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 ((interior (A : Set X)) ∪ interior (B : Set X)) ∧
      Topology.P2 ((interior (A : Set X)) ∪ interior (B : Set X)) ∧
        Topology.P3 ((interior (A : Set X)) ∪ interior (B : Set X)) := by
  -- Both `interior A` and `interior B` are open sets.
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hB : IsOpen (interior (B : Set X)) := isOpen_interior
  -- Their union is therefore open.
  have hOpen :
      IsOpen ((interior (A : Set X)) ∪ interior (B : Set X) : Set X) :=
    hA.union hB
  -- Every open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_has_all_Ps
      (X := X)
      (A := ((interior (A : Set X)) ∪ interior (B : Set X) : Set X))
      hOpen

theorem interior_nonempty_iff_nonempty_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A →
      ((interior (A : Set X)).Nonempty ↔ (A : Set X).Nonempty) := by
  intro hP1
  constructor
  · intro hInt
    exact hInt.mono (interior_subset : interior (A : Set X) ⊆ A)
  · intro hA
    exact
      (Topology.interior_nonempty_of_P1 (X := X) (A := A)) hP1 hA

theorem interior_closure_mono' {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) := by
  exact interior_mono (closure_mono hAB)

theorem subset_interior_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    (A : Set X) ⊆ interior (closure (A : Set X)) := by
  exact interior_maximal (subset_closure : (A : Set X) ⊆ closure (A : Set X)) hA

theorem P1_closure_iff_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (A : Set X)) ↔
      closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  simpa [closure_closure] using
    (Topology.P1_iff_closure_eq_closure_interior
      (X := X) (A := closure (A : Set X)))

theorem isOpen_closure_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP2_cl
  have hEquiv :=
    Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
  exact (hEquiv).1 hP2_cl

theorem closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  -- First, `closure A ⊆ univ` holds trivially.
  have h₁ : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro x _
    trivial
  -- Second, `univ ⊆ closure A` follows from the density hypothesis.
  have h₂ : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    have hMono : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    simpa [hDense] using hMono
  exact Set.Subset.antisymm h₁ h₂

theorem P1_of_subset_between {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (A : Set X) ⊆ B →
    B ⊆ closure (interior (A : Set X)) →
    Topology.P1 B := by
  intro hAB hBcl
  dsimp [Topology.P1] at *
  intro x hxB
  -- First, use the hypothesis `hBcl` to place `x` inside `closure (interior A)`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hBcl hxB
  -- Monotonicity: `interior A ⊆ interior B` because `A ⊆ B`.
  have hInt : interior (A : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  -- Taking closures preserves inclusions.
  have hCl : closure (interior (A : Set X)) ⊆
      closure (interior (B : Set X)) := closure_mono hInt
  -- Combine the facts to land in the desired target set.
  exact hCl hx_clA

theorem iUnion_closures_subset_closure_iUnion {X ι : Type*} [TopologicalSpace X]
    {F : ι → Set X} :
    (⋃ i, closure (F i : Set X)) ⊆ closure (⋃ i, F i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_cl⟩
  have h_sub : (F i : Set X) ⊆ ⋃ j, F j := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  have h_cl : closure (F i : Set X) ⊆ closure (⋃ j, F j : Set X) :=
    closure_mono h_sub
  exact h_cl hx_cl

theorem isOpen_closure_iff_P2_and_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure (A : Set X)) ↔
      (Topology.P2 (closure (A : Set X)) ∧ Topology.P3 (closure (A : Set X))) := by
  constructor
  · intro hOpen
    have hP2 : Topology.P2 (closure (A : Set X)) :=
      (Topology.isOpen_implies_P2 (X := X) (A := closure (A : Set X))) hOpen
    have hP3 : Topology.P3 (closure (A : Set X)) :=
      (Topology.isOpen_implies_P3 (X := X) (A := closure (A : Set X))) hOpen
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    have hEquiv :=
      Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
    exact (hEquiv).1 hP2

theorem P2_and_isClosed_iff_P3_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X)) :
    (Topology.P2 A ∧ IsClosed (A : Set X)) ↔
      (Topology.P3 A ∧ IsClosed (A : Set X)) := by
  -- Equivalence between `P2` and `P3` for closed sets.
  have hEquiv :=
    Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hClosed
  constructor
  · rintro ⟨hP2, hC⟩
    have hP3 : Topology.P3 A := hEquiv.1 hP2
    exact And.intro hP3 hC
  · rintro ⟨hP3, hC⟩
    have hP2 : Topology.P2 A := hEquiv.2 hP3
    exact And.intro hP2 hC

theorem interior_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      ((interior (A : Set X)).Nonempty ↔ (A : Set X).Nonempty) := by
  intro hP2
  constructor
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, (interior_subset : interior (A : Set X) ⊆ A) hxInt⟩
  · intro hA
    exact
      (Topology.interior_nonempty_of_P2 (X := X) (A := A)) hP2 hA

theorem P1_iff_P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ↔ Topology.P2 (Set.univ : Set X) := by
  have hAll := Topology.univ_has_all_Ps (X := X)
  rcases hAll with ⟨hP1, hP2, _⟩
  exact ⟨fun _ => hP2, fun _ => hP1⟩

theorem P3_closure_interior_iff_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  -- `closure (interior A)` is a closed set, so we can invoke the closed–open equivalence.
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (X := X)
      (A := closure (interior (A : Set X)))
      hClosed)

theorem P1_iff_P2_and_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔
      (Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X)) := by
  -- All three properties hold for the empty set, so the equivalence is immediate.
  have hP1 : Topology.P1 (∅ : Set X) := Topology.P1_empty (X := X)
  have hP2 : Topology.P2 (∅ : Set X) := Topology.P2_empty (X := X)
  have hP3 : Topology.P3 (∅ : Set X) := Topology.P3_empty (X := X)
  constructor
  · intro _; exact And.intro hP2 hP3
  · intro _; exact hP1

theorem union_three_interiors_subset_interior_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    (interior (A : Set X) ∪ interior (B : Set X) ∪ interior (C : Set X)) ⊆
      interior (A ∪ B ∪ C : Set X) := by
  intro x hx
  -- Split the triple union into cases.
  cases hx with
  | inl hAB =>
      -- `x ∈ interior A ∪ interior B`
      cases hAB with
      | inl hxA =>
          -- Case `x ∈ interior A`
          have hSub : (A : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inl hy)
          have hMono : interior (A : Set X) ⊆
              interior (A ∪ B ∪ C : Set X) := interior_mono hSub
          exact hMono hxA
      | inr hxB =>
          -- Case `x ∈ interior B`
          have hSub : (B : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inr hy)
          have hMono : interior (B : Set X) ⊆
              interior (A ∪ B ∪ C : Set X) := interior_mono hSub
          exact hMono hxB
  | inr hxC =>
      -- Case `x ∈ interior C`
      have hSub : (C : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inr hy
      have hMono : interior (C : Set X) ⊆
          interior (A ∪ B ∪ C : Set X) := interior_mono hSub
      exact hMono hxC

theorem interior_iUnion_eq_iUnion_of_open {X ι : Type*} [TopologicalSpace X]
    {F : ι → Set X} (hF : ∀ i, IsOpen (F i : Set X)) :
    interior (⋃ i, F i : Set X) = (⋃ i, F i : Set X) := by
  have hOpen : IsOpen (⋃ i, F i : Set X) := isOpen_iUnion (by
    intro i; exact hF i)
  simpa [hOpen.interior_eq]

theorem P3_of_isOpen_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P3 (closure (interior A)) := by
  have hEquiv :=
    Topology.P3_closure_interior_iff_isOpen_closure_interior
      (X := X) (A := A)
  exact (hEquiv).2 hOpen

theorem P2_iff_P1_and_P3_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (A : Set X)) ↔
      (Topology.P1 (interior (A : Set X)) ∧
        Topology.P3 (interior (A : Set X))) := by
  -- The set `interior A` is open.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  -- For open sets, `P1` and `P2` are equivalent.
  have h₁ :=
    Topology.P1_iff_P2_of_isOpen
      (X := X) (A := interior (A : Set X)) hOpen
  -- For open sets, `P2` and `P3` are equivalent.
  have h₂ :=
    Topology.P2_iff_P3_of_isOpen
      (X := X) (A := interior (A : Set X)) hOpen
  -- Assemble the desired equivalence.
  constructor
  · intro hP2
    -- Derive `P1` from `P2` using `h₁`.
    have hP1 : Topology.P1 (interior (A : Set X)) := (h₁).2 hP2
    -- Derive `P3` from `P2` using `h₂`.
    have hP3 : Topology.P3 (interior (A : Set X)) := (h₂).1 hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    -- Convert `P1` back into `P2` using `h₁`.
    exact (h₁).1 hP1

theorem P1_iff_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ↔ Topology.P3 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  simpa using
    (Topology.P1_iff_P3_of_isOpen (X := X) (A := (Set.univ : Set X)) hOpen)

theorem interior_closure_inter_left_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ closure (B : Set X)) : Set X)) ⊆
      interior (closure (B : Set X)) := by
  -- `A ∩ closure B` is contained in `closure B`.
  have hSub : (A ∩ closure (B : Set X) : Set X) ⊆ closure (B : Set X) := by
    intro x hx
    exact hx.2
  -- Apply `closure_mono` followed by `interior_mono`.
  simpa [closure_closure] using
    (interior_mono (closure_mono hSub))

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (A : Set X))) ⊆ closure (A : Set X) := by
  intro x hx
  -- First, `x` also belongs to `closure (interior A)` because
  -- `interior S ⊆ S` for every set `S`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := interior_subset hx
  -- Next, `closure (interior A)` is contained in `closure A` by monotonicity
  -- of `closure`, using the inclusion `interior A ⊆ A`.
  have h_subset :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Combining the two facts yields the claim.
  exact h_subset hx_cl

theorem isOpen_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    IsOpen ((A ∪ B ∪ C) : Set X) := by
  have hAB : IsOpen ((A ∪ B) : Set X) := hA.union hB
  simpa [Set.union_assoc] using hAB.union hC

theorem interior_closure_interior_nonempty_iff_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (interior (A : Set X)))).Nonempty ↔
      (interior (A : Set X)).Nonempty := by
  classical
  constructor
  · -- `←` direction: from non‐emptiness of the larger set deduce that of `interior A`.
    intro hIntCl
    -- A point in `interior (closure (interior A))` lies in `closure (interior A)`.
    have hCl : (closure (interior (A : Set X))).Nonempty := by
      rcases hIntCl with ⟨x, hx⟩
      exact ⟨x, interior_subset hx⟩
    -- Non‐emptiness of a closure is equivalent to that of the set itself.
    exact
      ((Topology.closure_nonempty_iff
          (X := X) (A := interior (A : Set X))).1) hCl
  · -- `→` direction: enlarge `interior A` using monotonicity.
    intro hIntA
    -- `interior A` sits inside `interior (closure (interior A))`.
    have hSub :
        (interior (A : Set X) : Set X) ⊆
          interior (closure (interior (A : Set X))) := by
      have hMono :
          interior (interior (A : Set X)) ⊆
            interior (closure (interior (A : Set X))) :=
        interior_mono
          (subset_closure :
            (interior (A : Set X)) ⊆ closure (interior (A : Set X)))
      simpa [interior_interior] using hMono
    -- Transfer any point of `interior A` along the inclusion.
    rcases hIntA with ⟨x, hxIntA⟩
    exact ⟨x, hSub hxIntA⟩

theorem closure_union_interiors_subset_union_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior (B : Set X)) ⊆
      closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) := by
  -- Step 1: Establish the inclusion before taking closures.
  have hSub :
      ((interior (A : Set X)) ∪ interior (B : Set X) : Set X) ⊆
        closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) := by
    intro x hx
    cases hx with
    | inl hxA => exact Or.inl (subset_closure hxA)
    | inr hxB => exact Or.inr (subset_closure hxB)
  -- Step 2: Apply `closure_mono`.
  have hIncl : closure (interior (A : Set X) ∪ interior (B : Set X)) ⊆
      closure (closure (interior (A : Set X)) ∪ closure (interior (B : Set X))) :=
    closure_mono hSub
  -- Step 3: The right‐hand side is already closed, so its closure is itself.
  have hClosedA : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  have hClosedB : IsClosed (closure (interior (B : Set X))) := isClosed_closure
  have hClosed :
      IsClosed (closure (interior (A : Set X)) ∪ closure (interior (B : Set X))) :=
    hClosedA.union hClosedB
  simpa [hClosed.closure_eq] using hIncl

theorem P2_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P2 (closure (B : Set X)) →
      Topology.P2 (closure (A ∪ B : Set X)) := by
  intro hA hB
  -- Apply the union lemma to the two closures.
  have hUnion :
      Topology.P2 (closure (A : Set X) ∪ closure (B : Set X)) :=
    Topology.P2_union (X := X)
      (A := closure (A : Set X)) (B := closure (B : Set X)) hA hB
  -- Re‐express the union of closures as the closure of the union.
  simpa [closure_union] using hUnion

theorem closure_inter_interiors_subset_inter_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X) ∩ interior (B : Set X)) : Set X) ⊆
      closure (interior (A : Set X)) ∩ closure (interior (B : Set X)) := by
  intro x hx
  -- The set `interior A ∩ interior B` is contained in `interior A`.
  have hSubA :
      ((interior (A : Set X)) ∩ interior (B : Set X) : Set X) ⊆
        interior (A : Set X) := by
    intro y hy; exact hy.1
  have hxA : x ∈ closure (interior (A : Set X)) :=
    (closure_mono hSubA) hx
  -- Likewise, it is contained in `interior B`.
  have hSubB :
      ((interior (A : Set X)) ∩ interior (B : Set X) : Set X) ⊆
        interior (B : Set X) := by
    intro y hy; exact hy.2
  have hxB : x ∈ closure (interior (B : Set X)) :=
    (closure_mono hSubB) hx
  exact And.intro hxA hxB

theorem closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simp [interior_univ, closure_univ]

theorem closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) ∪ interior (A : Set X) = closure (A : Set X) := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxCl => exact hxCl
    | inr hxInt =>
        have hxA : x ∈ (A : Set X) := interior_subset hxInt
        exact (subset_closure hxA)
  · intro hx
    exact Or.inl hx

theorem union_three_interiors_has_all_Ps {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    Topology.P1
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X)) ∧
      Topology.P2
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X)) ∧
        Topology.P3
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X)) := by
  -- The union of three open sets is open.
  have hOpen :
      IsOpen
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X) : Set X) := by
    have hAB :
        IsOpen
          ((interior (A : Set X)) ∪ interior (B : Set X) : Set X) :=
      (isOpen_interior).union isOpen_interior
    simpa [Set.union_assoc] using hAB.union isOpen_interior
  -- Every open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_has_all_Ps
      (X := X)
      (A :=
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X) : Set X))
      hOpen



theorem interior_inter_eq_empty_of_interiors_disjoint
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : interior (A : Set X) ∩ interior (B : Set X) = ∅) :
    interior ((A ∩ B) : Set X) = (∅ : Set X) := by
  -- `interior (A ∩ B)` is contained in `interior A ∩ interior B`.
  have hSub :
      (interior ((A ∩ B) : Set X) : Set X) ⊆
        interior (A : Set X) ∩ interior (B : Set X) :=
    Topology.interior_inter_subset_interiors (X := X) (A := A) (B := B)
  -- By the disjointness assumption, the right‐hand side is empty.
  have hSubEmpty :
      (interior ((A ∩ B) : Set X) : Set X) ⊆ (∅ : Set X) := by
    simpa [h] using hSub
  -- Conclude the desired equality of sets.
  exact Set.Subset.antisymm hSubEmpty (Set.empty_subset _)

theorem P3_iff_P1_and_P2_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (A : Set X)) ↔
      (Topology.P1 (interior (A : Set X)) ∧ Topology.P2 (interior (A : Set X))) := by
  -- `interior A` is an open set.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  -- Apply the already established equivalence for open sets.
  simpa using
    (Topology.P3_iff_P1_and_P2_of_isOpen
      (X := X) (A := interior (A : Set X)) hOpen)

theorem P2_iff_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) ↔ Topology.P3 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  simpa using
    (Topology.P2_iff_P3_of_isOpen (X := X) (A := (Set.univ : Set X)) hOpen)

theorem closure_inter_three_subset_inter_closures
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure ((A ∩ B ∩ C) : Set X) ⊆
      closure (A : Set X) ∩ closure (B : Set X) ∩ closure (C : Set X) := by
  intro x hx
  -- Each of `A`, `B`, and `C` contains `A ∩ B ∩ C`, hence their closures
  -- contain `closure (A ∩ B ∩ C)`.
  have hSubA : (A ∩ B ∩ C : Set X) ⊆ (A : Set X) := by
    intro y hy
    exact (hy.1).1
  have hSubB : (A ∩ B ∩ C : Set X) ⊆ (B : Set X) := by
    intro y hy
    exact (hy.1).2
  have hSubC : (A ∩ B ∩ C : Set X) ⊆ (C : Set X) := by
    intro y hy
    exact hy.2
  have hxA : x ∈ closure (A : Set X) := (closure_mono hSubA) hx
  have hxB : x ∈ closure (B : Set X) := (closure_mono hSubB) hx
  have hxC : x ∈ closure (C : Set X) := (closure_mono hSubC) hx
  exact And.intro (And.intro hxA hxB) hxC

theorem P2_closure_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P2 (closure (A : Set X)) →
    Topology.P2 (closure (B : Set X)) →
    Topology.P2 (closure (C : Set X)) →
    Topology.P2 (closure ((A ∪ B ∪ C) : Set X)) := by
  intro hA hB hC
  -- First, unite `closure A` and `closure B`.
  have hAB : Topology.P2 (closure ((A ∪ B) : Set X)) :=
    Topology.P2_closure_union (X := X) (A := A) (B := B) hA hB
  -- Next, unite the result with `closure C`.
  have hABC : Topology.P2 (closure (((A ∪ B) ∪ C) : Set X)) :=
    Topology.P2_closure_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABC

theorem P3_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (closure (A : Set X)) →
    Topology.P3 (closure (B : Set X)) →
    Topology.P3 (closure (A ∪ B : Set X)) := by
  intro hA hB
  -- Each hypothesis gives the openness of the corresponding closure.
  have hOpenA : IsOpen (closure (A : Set X)) :=
    (Topology.isOpen_closure_of_P3_closure (X := X) (A := A)) hA
  have hOpenB : IsOpen (closure (B : Set X)) :=
    (Topology.isOpen_closure_of_P3_closure (X := X) (A := B)) hB
  -- Hence their union, which equals `closure (A ∪ B)`, is open.
  have hOpenUnion : IsOpen (closure (A ∪ B : Set X)) := by
    have h : IsOpen ((closure (A : Set X)) ∪ closure (B : Set X) : Set X) :=
      hOpenA.union hOpenB
    simpa [closure_union] using h
  -- An open set satisfies `P3`.
  exact
    (Topology.P3_closure_of_isOpen_closure (X := X) (A := A ∪ B)) hOpenUnion

theorem P2_closure_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (closure (A : Set X))) ↔
      Topology.P2 (closure (A : Set X)) := by
  simpa [closure_closure]

theorem closure_interior_eq_self_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → closure (interior (A : Set X)) = A := by
  intro hP2
  -- From `P2` and the fact that `A` is closed, deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hClosed) hP2
  -- A clopen set satisfies `closure (interior A) = A`.
  exact
    Topology.closure_interior_eq_self_of_clopen
      (X := X) (A := A) hOpen hClosed

theorem interior_closure_nonempty_iff_nonempty_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      ((interior (closure (A : Set X))).Nonempty ↔ (A : Set X).Nonempty) := by
  intro hP3
  constructor
  · intro hInt
    exact
      (Topology.nonempty_of_interior_closure_nonempty
        (X := X) (A := A)) hInt
  · intro hA
    exact
      (Topology.interior_closure_nonempty_of_P3
        (X := X) (A := A)) hP3 hA

theorem P3_compl_iff_isOpen_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 (Aᶜ) ↔ IsOpen ((Aᶜ) : Set X) := by
  have hClosed : IsClosed ((Aᶜ) : Set X) := hA.isClosed_compl
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := (Aᶜ)) hClosed)

theorem closure_inter_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
  -- The set `A ∩ B` is contained in `A`.
  have hSub : (A ∩ B : Set X) ⊆ (A : Set X) := by
    intro x hx
    exact hx.1
  -- Taking closures preserves this inclusion.
  exact closure_mono hSub

theorem interior_closure_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      ((interior (closure (A : Set X))).Nonempty ↔ (A : Set X).Nonempty) := by
  intro hP2
  constructor
  · intro hInt
    exact
      (Topology.nonempty_of_interior_closure_nonempty
        (X := X) (A := A)) hInt
  · intro hA
    exact
      (Topology.interior_closure_nonempty_of_P2
        (X := X) (A := A)) hP2 hA

theorem P2_iff_forall_open_neighborhood {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔
      ∀ x ∈ (A : Set X), ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        U ⊆ interior (closure (interior (A : Set X))) := by
  dsimp [Topology.P2]
  constructor
  · intro hP2 x hxA
    exact
      ⟨interior (closure (interior (A : Set X))), isOpen_interior,
        hP2 hxA, subset_rfl⟩
  · intro h x hxA
    rcases h x hxA with ⟨U, _hUopen, hxU, hUsub⟩
    exact hUsub hxU

theorem iUnion_interior_closure_subset_interior_closure_iUnion
    {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (⋃ i, interior (closure (F i : Set X))) ⊆
      interior (closure (⋃ i, F i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxFi⟩
  have h_closure :
      closure (F i : Set X) ⊆ closure (⋃ j, F j : Set X) := by
    have h_subset : (F i : Set X) ⊆ ⋃ j, F j :=
      Set.subset_iUnion _ _
    exact closure_mono h_subset
  have h_mono :
      interior (closure (F i : Set X)) ⊆
        interior (closure (⋃ j, F j : Set X)) :=
    interior_mono h_closure
  exact h_mono hxFi

theorem interior_inter_three_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    interior ((A ∩ B ∩ C) : Set X) ⊆
      interior (A : Set X) ∩ interior (B : Set X) ∩ interior (C : Set X) := by
  intro x hx
  -- `A ∩ B ∩ C` is contained in each of `A`, `B`, and `C`.
  have hSubA : (A ∩ B ∩ C : Set X) ⊆ (A : Set X) := by
    intro y hy; exact hy.1.1
  have hSubB : (A ∩ B ∩ C : Set X) ⊆ (B : Set X) := by
    intro y hy; exact (hy.1).2
  have hSubC : (A ∩ B ∩ C : Set X) ⊆ (C : Set X) := by
    intro y hy; exact hy.2
  -- Apply monotonicity of `interior` to transfer the membership.
  have hxA : x ∈ interior (A : Set X) := (interior_mono hSubA) hx
  have hxB : x ∈ interior (B : Set X) := (interior_mono hSubB) hx
  have hxC : x ∈ interior (C : Set X) := (interior_mono hSubC) hx
  exact And.intro (And.intro hxA hxB) hxC

theorem closed_P2_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  intro hP2
  -- A closed set with property `P2` is open, by a previously established lemma.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hClosed) hP2
  -- A clopen set satisfies all three properties `P1`, `P2`, and `P3`.
  exact Topology.clopen_has_all_Ps (X := X) (A := A) hOpen hClosed

theorem P1_inter_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → IsOpen (B : Set X) → Topology.P1 (A ∩ B) := by
  classical
  intro hP1A hOpenB
  dsimp [Topology.P1] at hP1A ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in the closure of `interior A`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hP1A hxA
  -- We show that `x` also belongs to the closure of `interior A ∩ B`.
  have hx_clAB : x ∈ closure ((interior (A : Set X)) ∩ B) := by
    -- Use the characterisation of closure via neighbourhoods.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighbourhood `U ∩ B` of `x`.
    have hUBopen : IsOpen (U ∩ B) := hUopen.inter hOpenB
    have hxUB : x ∈ U ∩ B := And.intro hxU hxB
    -- Since `x ∈ closure (interior A)`, the intersection with `interior A` is nonempty.
    have hNonempty :
        ((U ∩ B) ∩ interior (A : Set X)).Nonempty :=
      (mem_closure_iff).1 hx_clA (U ∩ B) hUBopen hxUB
    -- Rearrange the intersection to fit the required shape.
    simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm,
      Set.inter_right_comm] using hNonempty
  -- Because `B` is open, `interior (A ∩ B) = interior A ∩ B`.
  have hInt_eq :
      interior ((A ∩ B) : Set X) = (interior (A : Set X)) ∩ B :=
    interior_inter_right_open (X := X) (A := A) (B := B) hOpenB
  -- Re‐express the previous membership with the identified interior.
  have : x ∈ closure (interior ((A ∩ B) : Set X)) := by
    simpa [hInt_eq] using hx_clAB
  exact this

theorem P3_closure_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P3 (closure (A : Set X)) →
    Topology.P3 (closure (B : Set X)) →
    Topology.P3 (closure (C : Set X)) →
    Topology.P3 (closure ((A ∪ B ∪ C) : Set X)) := by
  intro hA hB hC
  -- First, unite the closures of `A` and `B`.
  have hAB : Topology.P3 (closure ((A ∪ B) : Set X)) :=
    Topology.P3_closure_union (X := X) (A := A) (B := B) hA hB
  -- Next, unite the result with the closure of `C`.
  have hABC : Topology.P3 (closure (((A ∪ B) ∪ C) : Set X)) :=
    Topology.P3_closure_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the desired form.
  simpa [Set.union_assoc] using hABC

theorem P1_inter_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen (A : Set X) → Topology.P1 B → Topology.P1 (A ∩ B) := by
  intro hOpenA hP1B
  -- Apply the existing “right‐open” lemma after swapping the factors
  have h := Topology.P1_inter_right_of_open (X := X) (A := B) (B := A) hP1B hOpenA
  simpa [Set.inter_comm] using h

theorem nonempty_of_interior_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty → (A : Set X).Nonempty := by
  rintro ⟨x, hxInt⟩
  exact ⟨x, interior_subset hxInt⟩

theorem P3_inter_four_of_open {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) (hD : IsOpen (D : Set X)) :
    Topology.P3 (A ∩ B ∩ C ∩ D) := by
  -- The four‐fold intersection of open sets is open.
  have hOpen : IsOpen ((A ∩ B ∩ C ∩ D) : Set X) :=
    (((hA.inter hB).inter hC).inter hD)
  -- Every open set satisfies `P3`.
  exact
    (Topology.isOpen_has_all_Ps
      (X := X)
      (A := (A ∩ B ∩ C ∩ D : Set X))
      hOpen).2.2

theorem interior_closure_union_three_eq {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    interior (closure ((A ∪ B ∪ C) : Set X)) =
      interior (closure (A : Set X) ∪ closure (B : Set X) ∪ closure (C : Set X)) := by
  calc
    interior (closure ((A ∪ B ∪ C) : Set X)) =
        interior (closure (((A ∪ B) ∪ C) : Set X)) := by
          simpa [Set.union_assoc]
    _ = interior (closure ((A ∪ B) : Set X) ∪ closure (C : Set X)) := by
          simpa using
            (interior_closure_union_eq (X := X) (A := A ∪ B) (B := C))
    _ = interior ((closure (A : Set X) ∪ closure (B : Set X)) ∪
        closure (C : Set X)) := by
          have h_cl :
              closure ((A ∪ B) : Set X) =
                closure (A : Set X) ∪ closure (B : Set X) := by
            simpa [closure_union]
          simpa [h_cl]
    _ = interior (closure (A : Set X) ∪ closure (B : Set X) ∪
        closure (C : Set X)) := by
          simpa [Set.union_assoc]

theorem open_union_three_has_all_Ps {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    Topology.P1 (A ∪ B ∪ C) ∧ Topology.P2 (A ∪ B ∪ C) ∧ Topology.P3 (A ∪ B ∪ C) := by
  -- The triple union of open sets is open.
  have hOpen : IsOpen ((A ∪ B ∪ C) : Set X) :=
    isOpen_union_three hA hB hC
  -- Every open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_has_all_Ps
      (X := X) (A := ((A ∪ B ∪ C) : Set X)) hOpen

theorem P3_inter_four_of_closed {X : Type*} [TopologicalSpace X]
    {A B C D : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X))
    (hC : IsClosed (C : Set X)) (hD : IsClosed (D : Set X)) :
    Topology.P3 A → Topology.P3 B → Topology.P3 C → Topology.P3 D →
      Topology.P3 (A ∩ B ∩ C ∩ D) := by
  intro hPA hPB hPC hPD
  -- From `P3` on closed sets, obtain that each set is open.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := B) hB).1 hPB
  have hOpenC : IsOpen (C : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := C) hC).1 hPC
  have hOpenD : IsOpen (D : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := D) hD).1 hPD
  -- The intersection of four open sets is open.
  have hOpenInter : IsOpen ((A ∩ B ∩ C ∩ D) : Set X) :=
    (((hOpenA.inter hOpenB).inter hOpenC).inter hOpenD)
  -- Every open set satisfies `P3`.
  exact
    (Topology.isOpen_has_all_Ps
        (X := X)
        (A := (A ∩ B ∩ C ∩ D : Set X))
        hOpenInter).2.2

theorem closure_interior_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ B) ⊆ closure (A ∪ B : Set X) := by
  -- First, show the required subset relation before taking closures.
  have hSub :
      ((interior (A : Set X)) ∪ B : Set X) ⊆ A ∪ B := by
    intro x hx
    cases hx with
    | inl hxIntA => exact Or.inl (interior_subset hxIntA)
    | inr hxB    => exact Or.inr hxB
  -- Taking closures preserves inclusions.
  exact closure_mono hSub

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 D →
      Topology.P2 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  have hAB : Topology.P2 (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  have hABC : Topology.P2 ((A ∪ B) ∪ C) :=
    Topology.P2_union (X := X) (A := A ∪ B) (B := C) hAB hC
  have hABCD : Topology.P2 (((A ∪ B) ∪ C) ∪ D) :=
    Topology.P2_union (X := X) (A := (A ∪ B) ∪ C) (B := D) hABC hD
  simpa [Set.union_assoc] using hABCD

theorem P1_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 D →
      Topology.P1 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- First, unite `A`, `B`, and `C`.
  have hABC : Topology.P1 (A ∪ B ∪ C) :=
    Topology.P1_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Next, union the result with `D`.
  have hABCD : Topology.P1 ((A ∪ B ∪ C) ∪ D) :=
    Topology.P1_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABCD

theorem P1_closure_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (closure (interior (A : Set X)) ∪ closure (interior (B : Set X))) := by
  -- `P1` holds for each `closure (interior A)` and `closure (interior B)`.
  have hA : Topology.P1 (closure (interior (A : Set X))) :=
    Topology.closure_interior_has_P1 (X := X) (A := A)
  have hB : Topology.P1 (closure (interior (B : Set X))) :=
    Topology.closure_interior_has_P1 (X := X) (A := B)
  -- Combine the two sets using the existing union lemma for `P1`.
  exact
    Topology.P1_union
      (X := X)
      (A := closure (interior (A : Set X)))
      (B := closure (interior (B : Set X)))
      hA hB

theorem closure_inter_subset_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
  -- Since `A ∩ B ⊆ B`, applying `closure_mono` gives the desired inclusion.
  have hSub : (A ∩ B : Set X) ⊆ (B : Set X) := by
    intro x hx
    exact hx.2
  exact closure_mono hSub

theorem P2_inter_four_of_open {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) (hD : IsOpen (D : Set X)) :
    Topology.P2 (A ∩ B ∩ C ∩ D) := by
  -- The intersection of four open sets is open.
  have hOpen : IsOpen ((A ∩ B ∩ C ∩ D) : Set X) :=
    (((hA.inter hB).inter hC).inter hD)
  -- Every open set satisfies `P2`.
  exact
    (Topology.isOpen_has_all_Ps
        (X := X)
        (A := (A ∩ B ∩ C ∩ D : Set X))
        hOpen).2.1

theorem P3_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    Topology.P3 A ↔ interior (A : Set X) = A := by
  -- First, relate `P3` for a closed set to the openness of the set.
  have h₁ : Topology.P3 A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA
  -- Second, characterize openness by equality with the interior.
  have h₂ : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hIntEq
      -- Since `interior A` is open and equals `A`, the latter is open.
      have hOpenInt : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using hOpenInt
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem P3_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 C → Topology.P3 D →
    Topology.P3 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- Unite `A` and `B`.
  have hAB : Topology.P3 (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Unite the result with `C`.
  have hABC : Topology.P3 ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Finally, unite with `D`.
  have hABCD : Topology.P3 (((A ∪ B) ∪ C) ∪ D) :=
    Topology.P3_union (X := X) (A := (A ∪ B) ∪ C) (B := D) hABC hD
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABCD

theorem P2_and_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    (Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen (A : Set X) := by
  -- Equivalences of `P2` and `P3` with openness for a closed set.
  have hP2 : Topology.P2 A ↔ IsOpen (A : Set X) :=
    Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA
  have hP3 : Topology.P3 A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA
  -- Assemble the desired equivalence.
  constructor
  · rintro ⟨hP2A, _⟩
    exact (hP2).1 hP2A
  · intro hOpen
    have hAll := Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen
    exact And.intro hAll.2.1 hAll.2.2

theorem P1_inter_four_of_open {X : Type*} [TopologicalSpace X]
    {A B C D : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) (hD : IsOpen (D : Set X)) :
    Topology.P1 (A ∩ B ∩ C ∩ D) := by
  -- The intersection of four open sets is open.
  have hOpen : IsOpen ((A ∩ B ∩ C ∩ D) : Set X) :=
    (((hA.inter hB).inter hC).inter hD)
  -- Every open set satisfies `P1`.
  exact
    (Topology.isOpen_has_all_Ps
        (X := X)
        (A := (A ∩ B ∩ C ∩ D : Set X))
        hOpen).1

theorem isOpen_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) (hD : IsOpen (D : Set X)) :
    IsOpen ((A ∪ B ∪ C ∪ D) : Set X) := by
  -- First, the union `A ∪ B ∪ C` is open.
  have hABC : IsOpen ((A ∪ B ∪ C) : Set X) := by
    have hAB : IsOpen ((A ∪ B) : Set X) := hA.union hB
    simpa [Set.union_assoc] using hAB.union hC
  -- Adding `D` preserves openness.
  simpa [Set.union_assoc] using hABC.union hD

theorem closures_union_four_eq_closure_union_four {X : Type*} [TopologicalSpace X]
    {A B C D : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ∪ closure (C : Set X) ∪ closure (D : Set X) =
      closure (A ∪ B ∪ C ∪ D : Set X) := by
  calc
    (closure (A : Set X)) ∪ closure (B : Set X) ∪ closure (C : Set X) ∪ closure (D : Set X)
        = ((closure (A : Set X) ∪ closure (B : Set X)) ∪ closure (C : Set X)) ∪
            closure (D : Set X) := by
          simpa [Set.union_assoc]
    _ = (closure (A ∪ B : Set X) ∪ closure (C : Set X)) ∪ closure (D : Set X) := by
          simpa [closure_union]
    _ = closure (A ∪ B ∪ C : Set X) ∪ closure (D : Set X) := by
          simpa [Set.union_assoc, closure_union]
    _ = closure ((A ∪ B ∪ C) ∪ D : Set X) := by
          simpa [closure_union]
    _ = closure (A ∪ B ∪ C ∪ D : Set X) := by
          simpa [Set.union_assoc]

theorem union_four_interiors_subset_interior_union_four
    {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    (interior (A : Set X) ∪ interior (B : Set X) ∪
        interior (C : Set X) ∪ interior (D : Set X)) ⊆
      interior (A ∪ B ∪ C ∪ D : Set X) := by
  intro x hx
  -- Split membership in the four‐way union into two cases.
  -- 1. `x` belongs to one of the first three interiors.
  -- 2. `x` belongs to `interior D`.
  cases hx with
  | inl hABC =>
      -- Reinterpret `hABC` as membership in `interior A ∪ interior B ∪ interior C`.
      have hABC' :
          x ∈ (interior (A : Set X) ∪ interior (B : Set X) ∪
              interior (C : Set X)) := by
        simpa [Set.union_assoc] using hABC
      -- Apply the existing three‐set lemma.
      have h₁ :=
        (Topology.union_three_interiors_subset_interior_union_three
            (X := X) (A := A) (B := B) (C := C)) hABC'
      -- Enlarge the target from the triple to the quadruple union.
      have hMono :
          interior (A ∪ B ∪ C : Set X) ⊆
            interior (A ∪ B ∪ C ∪ D : Set X) := by
        have hSub :
            (A ∪ B ∪ C : Set X) ⊆ (A ∪ B ∪ C ∪ D : Set X) := by
          intro y hy
          -- Interpret the right‐hand side as `(A ∪ B ∪ C) ∪ D`.
          have : y ∈ ((A ∪ B ∪ C) ∪ D : Set X) := Or.inl hy
          simpa [Set.union_assoc] using this
        exact interior_mono hSub
      exact hMono h₁
  | inr hD =>
      -- `x` lies in `interior D`; enlarge the target as in the previous case.
      have hSub :
          (D : Set X) ⊆ (A ∪ B ∪ C ∪ D : Set X) := by
        intro y hy
        have : y ∈ ((A ∪ B ∪ C) ∪ D : Set X) := Or.inr hy
        simpa [Set.union_assoc] using this
      have hMono :
          interior (D : Set X) ⊆
            interior (A ∪ B ∪ C ∪ D : Set X) :=
        interior_mono hSub
      exact hMono hD

theorem P3_implies_P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P3 (interior (A : Set X)) := by
  intro hP3
  -- Step 1:  From `P3 A`, obtain `P2 (interior A)`.
  have hP2_int : Topology.P2 (interior (A : Set X)) :=
    (Topology.P3_implies_P2_interior (X := X) (A := A)) hP3
  -- Step 2:  For the open set `interior A`, `P2` is equivalent to `P3`.
  have hEquiv :=
    (Topology.P2_iff_P3_of_interior (X := X) (A := A))
  exact (hEquiv).1 hP2_int

theorem P2_inter_four_of_closed {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hC_closed : IsClosed (C : Set X)) (hD_closed : IsClosed (D : Set X)) :
    Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 D →
      Topology.P2 (A ∩ B ∩ C ∩ D) := by
  intro hPA hPB hPC hPD
  -- Convert each `P2` on a closed set into openness.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed) hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := B) hB_closed) hPB
  have hOpenC : IsOpen (C : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := C) hC_closed) hPC
  have hOpenD : IsOpen (D : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := D) hD_closed) hPD
  -- The intersection of four open sets is open, hence satisfies `P2`.
  exact
    (Topology.P2_inter_four_of_open (X := X) (A := A) (B := B) (C := C) (D := D)
        hOpenA hOpenB hOpenC hOpenD)

theorem closure_interior_eq_self_of_isClosed_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P1 A → closure (interior (A : Set X)) = A := by
  intro hP1
  -- `P1` gives `closure A = closure (interior A)`.
  have hEq :=
    (Topology.P1_iff_closure_eq_closure_interior
        (X := X) (A := A)).1 hP1
  -- Since `A` is closed, `closure A = A`.
  have hCl : closure (A : Set X) = A := hClosed.closure_eq
  -- Combine the two equalities.
  have h : (A : Set X) = closure (interior (A : Set X)) := by
    simpa [hCl] using hEq
  simpa using h.symm

theorem closure_interior_closure_nonempty_iff_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior (closure (A : Set X)))).Nonempty ↔
      (interior (closure (A : Set X))).Nonempty := by
  simpa using
    (Topology.closure_nonempty_iff
      (X := X)
      (A := interior (closure (A : Set X))))

theorem P1_closure_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 D →
      Topology.P1 (closure (A ∪ B ∪ C ∪ D : Set X)) := by
  intro hA hB hC hD
  -- First, obtain `P1` for the four‐fold union.
  have hUnion : Topology.P1 (A ∪ B ∪ C ∪ D) :=
    Topology.P1_union_four (X := X) (A := A) (B := B) (C := C) (D := D) hA hB hC hD
  -- Taking the closure preserves `P1`.
  have hClosure : Topology.P1 (closure ((A ∪ B ∪ C ∪ D) : Set X)) :=
    Topology.P1_implies_P1_closure (X := X) (A := A ∪ B ∪ C ∪ D) hUnion
  -- Reassociate unions to match the goal statement.
  simpa [Set.union_assoc] using hClosure