

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  exact hP2.trans interior_subset

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hcl : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have hint : interior (closure (interior A)) ⊆ interior (closure A) := interior_mono hcl
  exact hP2.trans hint

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  exact ⟨P2_implies_P1 hP2, P2_implies_P3 hP2⟩

theorem P3_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  dsimp [Topology.P3]
  simpa [interior_interior] using
    (interior_mono (subset_closure : interior A ⊆ closure (interior A)))

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : A ⊆ closure A)
  simpa [hA.interior_eq] using hsubset

theorem P2_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  simpa [interior_interior] using
    (interior_mono (subset_closure : interior A ⊆ closure (interior A)))

theorem P1_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  simpa [interior_interior] using
    (subset_closure : interior A ⊆ closure (interior A))

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  simpa [hA.interior_eq] using (subset_closure : (A : Set X) ⊆ closure A)

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  simpa [hA.interior_eq] using hsubset

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) : closure A = closure (interior A) := by
  apply subset_antisymm
  ·
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using this
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : closure A = closure (interior A) := by
  apply subset_antisymm
  ·
    have h₁ : A ⊆ closure (interior A) := by
      calc
        A ⊆ interior (closure (interior A)) := h
        _ ⊆ closure (interior A) := interior_subset
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h₁
    simpa [closure_closure] using this
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro h
    exact Topology.closure_eq_closure_interior_of_P1 h
  · intro hEq
    dsimp [Topology.P1]
    have hsubset : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq] using hsubset

theorem P2_of_P3_and_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hEq : closure A = closure (interior A)) :
    Topology.P2 A := by
  dsimp [Topology.P2, Topology.P3] at *
  have hsubset : interior (closure A) ⊆ interior (closure (interior A)) := by
    simpa [hEq]
  exact hP3.trans hsubset

theorem P2_iff_P3_and_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A ↔ (Topology.P3 A ∧ closure A = closure (interior A)) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A := P2_implies_P3 hP2
    have hEq : closure A = closure (interior A) := closure_eq_closure_interior_of_P2 hP2
    exact ⟨hP3, hEq⟩
  · rintro ⟨hP3, hEq⟩
    exact P2_of_P3_and_closure_eq_closure_interior hP3 hEq

theorem P1_of_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) := by
  dsimp [Topology.P1]
  simpa [interior_interior] using
    (subset_closure : interior (closure A) ⊆ closure (interior (closure A)))

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 A ∧ Topology.P3 A) → Topology.P2 A := by
  rintro ⟨hP1, hP3⟩
  have hEq : closure A = closure (interior A) :=
    (Topology.closure_eq_closure_interior_of_P1 hP1)
  exact Topology.P2_of_P3_and_closure_eq_closure_interior hP3 hEq

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1_and_P3 hP2
  · intro hPair
    exact P2_of_P1_and_P3 hPair

theorem P3_of_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  simpa using Topology.P3_of_open (A := interior (closure A)) isOpen_interior

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hAx =>
      -- `x ∈ A`, use `hA` to send it into the desired closure
      have hxA : x ∈ closure (interior A) := hA hAx
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA
  | inr hBx =>
      -- `x ∈ B`, use `hB` to send it into the desired closure
      have hxB : x ∈ closure (interior B) := hB hBx
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB : Topology.P3 B) :
    Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure A) := hA hAx
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure B) := hB hBx
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  have hP1A : Topology.P1 A := Topology.P2_implies_P1 hA
  have hP1B : Topology.P1 B := Topology.P2_implies_P1 hB
  have hP3A : Topology.P3 A := Topology.P2_implies_P3 hA
  have hP3B : Topology.P3 B := Topology.P2_implies_P3 hB
  have hP1Union : Topology.P1 (A ∪ B) := Topology.P1_union hP1A hP1B
  have hP3Union : Topology.P3 (A ∪ B) := Topology.P3_union hP3A hP3B
  exact Topology.P2_of_P1_and_P3 (A := A ∪ B) ⟨hP1Union, hP3Union⟩

theorem interior_closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    interior (closure A) = interior (closure (interior A)) := by
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) h
  simpa [hEq]

theorem P2_of_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure A)) := by
  simpa using
    (Topology.P2_of_open (A := interior (closure A)) isOpen_interior)

theorem interior_closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : Topology.P2 A) :
    interior (closure A) = interior (closure (interior A)) := by
  have hEq : closure A = closure (interior A) :=
    closure_eq_closure_interior_of_P2 (A := A) h
  simpa [hEq]

theorem P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) : Topology.P1 (closure A) := by
  dsimp [Topology.P1] at h ⊢
  -- Step 1: `closure (interior A)` is contained in the target closure.
  have h2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Step 2: Combine with `h` to obtain a subset relation for `A`.
  have hcomb : (A : Set X) ⊆ closure (interior (closure A)) := h.trans h2
  -- Step 3: Take closures to upgrade the subset relation from `A` to `closure A`.
  have hfinal : closure A ⊆ closure (interior (closure A)) := by
    have : closure A ⊆ closure (closure (interior (closure A))) := closure_mono hcomb
    simpa [closure_closure] using this
  exact hfinal

theorem P1_of_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- We first establish the necessary subset relation.
  have hsubset : closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    apply closure_mono
    -- Since `interior A` is an open subset of `closure (interior A)`,
    -- it is contained in the interior of that closure.
    have : (interior A : Set X) ⊆ interior (closure (interior A)) := by
      apply interior_maximal
      · exact subset_closure
      · exact isOpen_interior
    exact this
  exact hsubset hx

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  simp [interior_univ, closure_univ]

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  cases hx

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  simp

theorem P1_of_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) := by
  simpa using
    (Topology.P1_of_open (A := interior (closure (interior A))) isOpen_interior)

theorem interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hne : A.Nonempty) : (interior A).Nonempty := by
  classical
  by_contra hInt
  -- If `interior A` is empty, rewrite it to `∅`.
  have hIntEq : interior A = (∅ : Set X) := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have : (interior A).Nonempty := ⟨x, hx⟩
    exact (hInt this).elim
  -- Pick an element of `A` and send it through the `P2` containment.
  rcases hne with ⟨x, hxA⟩
  have hxInner : x ∈ interior (closure (interior A)) := hP2 hxA
  -- The rewritten set is empty, giving a contradiction.
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEq] using hxInner
  exact (Set.not_mem_empty x) this

theorem closure_interior_eq_of_closed_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP1 : Topology.P1 A) :
    closure (interior A) = A := by
  apply subset_antisymm
  ·
    have hIntSub : interior A ⊆ (A : Set X) := interior_subset
    exact closure_minimal hIntSub hA
  ·
    exact hP1

theorem P2_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P2 (interior A) := by
  intro hP2
  dsimp [Topology.P2] at hP2 ⊢
  intro x hx
  -- `hx` gives `x ∈ interior A`, hence `x ∈ A`
  have hxA : x ∈ A := (interior_subset : interior A ⊆ A) hx
  -- Use `hP2` to send `x` into the larger interior
  have hxTarget : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Rewrite the goal using `interior_interior`
  simpa [interior_interior] using hxTarget

theorem interior_closure_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : x ∈ interior (closure A) := by
    have hsubset : closure (A ∩ B) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact (interior_mono hsubset) hx
  have hB : x ∈ interior (closure B) := by
    have hsubset : closure (A ∩ B) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact (interior_mono hsubset) hx
  exact ⟨hA, hB⟩

theorem closure_eq_closure_interior_of_P1_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) :
    closure (A ∪ B) = closure (interior (A ∪ B)) := by
  have hUnion : Topology.P1 (A ∪ B) := Topology.P1_union hA hB
  exact Topology.closure_eq_closure_interior_of_P1 (A := A ∪ B) hUnion

theorem P2_of_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior A))) := by
  simpa using
    (Topology.P2_of_open (A := interior (closure (interior A))) isOpen_interior)

theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hne : A.Nonempty) : (interior A).Nonempty := by
  classical
  -- Assume, for a contradiction, that `interior A` is empty.
  by_contra hInt
  have hIntEq : interior A = (∅ : Set X) := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have : (interior A).Nonempty := ⟨x, hx⟩
    exact (hInt this).elim
  -- Pick an element of `A`.
  rcases hne with ⟨x, hxA⟩
  -- Use `P1` to map it into the closure of the interior.
  have hxClosure : x ∈ closure (interior A) := hP1 hxA
  -- Contradiction with the fact that the interior is empty.
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEq] using hxClosure
  exact (Set.not_mem_empty x) this

theorem interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hne : A.Nonempty) : (interior (closure A)).Nonempty := by
  rcases hne with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩

theorem closure_interior_eq_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : closure (interior A) = closure A := by
  simpa [hA.interior_eq]

theorem P1_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i)) :
    Topology.P1 (⋃ i, A i) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  have hxClosure : x ∈ closure (interior (A i)) := (hA i) hxAi
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    apply closure_mono
    have hinner : interior (A i) ⊆ interior (⋃ j, A j) := by
      have hsub : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.mpr ⟨i, hy⟩
      exact interior_mono hsub
    exact hinner
  exact hsubset hxClosure

theorem P3_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P3 (A i)) :
    Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  have hxInterior : x ∈ interior (closure (A i)) := (hA i) hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    apply interior_mono
    have hclsubset : closure (A i) ⊆ closure (⋃ j, A j) := by
      apply closure_mono
      exact Set.subset_iUnion _ _
    exact hclsubset
  exact hsubset hxInterior

theorem P2_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P2 (A i)) :
    Topology.P2 (⋃ i, A i) := by
  -- Obtain `P1` and `P3` for each `A i`.
  have hP1 : ∀ i, Topology.P1 (A i) := fun i => Topology.P2_implies_P1 (hA i)
  have hP3 : ∀ i, Topology.P3 (A i) := fun i => Topology.P2_implies_P3 (hA i)
  -- Deduce `P1` and `P3` for the union.
  have hP1Union : Topology.P1 (⋃ i, A i) := Topology.P1_iUnion hP1
  have hP3Union : Topology.P3 (⋃ i, A i) := Topology.P3_iUnion hP3
  -- Conclude `P2` for the union.
  exact Topology.P2_of_P1_and_P3 (A := ⋃ i, A i) ⟨hP1Union, hP3Union⟩

theorem closure_interior_eq_of_closed_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.closure_interior_eq_of_closed_P1 hA hP1

theorem P3_iff_open_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    have hsubset : (A : Set X) ⊆ interior A := by
      -- Rewrite `interior (closure A)` using `hA.closure_eq`.
      have h : (A : Set X) ⊆ interior (closure A) := hP3
      simpa [hA.closure_eq] using h
    have hEq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact hsubset
    -- Since `interior A` is open, `A` is open as well.
    have : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using this
  · intro hOpen
    exact Topology.P3_of_open (A := A) hOpen

theorem P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.P1_closure_of_P1 hP1

theorem P1_closed_iff_closure_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_of_closed_P1 (A := A) hA hP1
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    have : x ∈ closure (interior A) := by
      simpa [hEq] using hx
    exact this

theorem interior_closure_iInter_subset {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- For each `i`, we show `x ∈ interior (closure (A i))`.
  have hxAll : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- Establish `closure (⋂ i, A i) ⊆ closure (A i)`.
    have hsubset : closure (⋂ j, A j) ⊆ closure (A i) := by
      apply closure_mono
      intro y hy
      have hmem : (∀ j, y ∈ A j) := (Set.mem_iInter.1 hy)
      exact hmem i
    -- Transfer membership via `interior_mono`.
    exact (interior_mono hsubset) hx
  -- Collect the witnesses for every `i` into the intersection.
  exact Set.mem_iInter.2 hxAll

theorem interior_eq_self_of_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  apply subset_antisymm
  · exact interior_subset
  ·
    have h : (A : Set X) ⊆ interior (closure A) := hP3
    simpa [hA.closure_eq] using h

theorem interior_closure_interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hne : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  rcases hne with ⟨x, hxA⟩
  exact ⟨x, hP2 hxA⟩

theorem P2_iff_open_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ IsOpen A := by
  -- Relate `P3` and openness for closed sets.
  have hP3Open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_open_of_closed (A := A) hA
  constructor
  · intro hP2
    -- `P2` implies `P3`, then use the equivalence.
    have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
    exact (hP3Open.mp hP3)
  · intro hOpen
    -- An open set satisfies `P2`.
    exact Topology.P2_of_open (A := A) hOpen

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  have h₁ : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_iff_open_of_closed (A := A) hA
  have h₂ : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_open_of_closed (A := A) hA
  simpa using h₁.trans h₂.symm

theorem P2_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ Topology.P3 (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P2_iff_P3_of_closed (A := closure A) hClosed)

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _; exact Topology.P2_of_open (A := A) hA
  · intro _; exact Topology.P1_of_open (A := A) hA

theorem interior_closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have hcl : closure A ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact hcl
      exact hsubset hAx
  | inr hBx =>
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have hcl : closure B ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact hcl
      exact hsubset hBx

theorem P1_of_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure A))) := by
  -- First, `interior (closure A)` satisfies `P1`.
  have hInt : Topology.P1 (interior (closure A)) := by
    simpa using Topology.P1_of_interior_closure (A := A)
  -- Taking the closure preserves `P1`.
  have hCl : Topology.P1 (closure (interior (closure A))) :=
    Topology.P1_closure_of_P1 (A := interior (closure A)) hInt
  simpa using hCl

theorem P3_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hxA
  have hxCl : x ∈ closure A := subset_closure hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3 hxCl
  simpa [closure_closure] using hxInt

theorem P3_of_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior A))) := by
  simpa using
    (Topology.P3_of_open (A := interior (closure (interior A))) isOpen_interior)

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P1_of_open (A := A) hA
  have hP3 : Topology.P3 A := Topology.P3_of_open (A := A) hA
  exact ⟨fun _ => hP3, fun _ => hP1⟩

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  simpa using
    ((Topology.P1_iff_P2_of_open (A := A) hA).symm.trans
      (Topology.P1_iff_P3_of_open (A := A) hA))

theorem interior_closure_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hne : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
  exact Topology.interior_closure_nonempty_of_P3 hP3 hne

theorem closure_interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : (interior A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          exact Set.subset_union_left
        exact this
      exact hsubset hA
  | inr hB =>
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : (interior B : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          exact Set.subset_union_right
        exact this
      exact hsubset hB

theorem P123_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.P1_of_open (A := A) hA,
      Topology.P2_of_open (A := A) hA,
      Topology.P3_of_open (A := A) hA⟩

theorem closure_interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show membership in the first component.
  have hA : x ∈ closure (interior A) := by
    have hsubset : closure (interior (A ∩ B)) ⊆ closure (interior A) := by
      apply closure_mono
      exact interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact hsubset hx
  -- Show membership in the second component.
  have hB : x ∈ closure (interior B) := by
    have hsubset : closure (interior (A ∩ B)) ⊆ closure (interior B) := by
      apply closure_mono
      exact interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact hsubset hx
  exact ⟨hA, hB⟩

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure A = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  simpa [hDense, interior_univ] using (Set.mem_univ x)

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have : x ∈ (Set.univ : Set X) := Set.mem_univ x
  simpa [hDense, interior_univ] using this

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hxA
  have : x ∈ (Set.univ : Set X) := Set.mem_univ x
  simpa [hDense] using this

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  -- `x` certainly belongs to the interior of `closure (interior A)` because that set is `⊤`.
  have hxInt : x ∈ interior (closure (interior A)) := by
    have : x ∈ (Set.univ : Set X) := Set.mem_univ x
    simpa [hDense, interior_univ] using this
  -- Monotonicity of `interior` and `closure` lets us upgrade the membership.
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono (interior_subset : interior A ⊆ A)
  exact hsubset hxInt

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → Topology.P3 A) :
    Topology.P3 (⋃₀ 𝔄) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hxInt : x ∈ interior (closure A) := hA A hA_mem hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝔄)) := by
    apply interior_mono
    have : closure A ⊆ closure (⋃₀ 𝔄) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact this
  exact hsubset hxInt

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → Topology.P1 A) :
    Topology.P1 (⋃₀ 𝔄) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hxCl : x ∈ closure (interior A) := hA A hA_mem hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝔄)) := by
    apply closure_mono
    have : interior A ⊆ interior (⋃₀ 𝔄) := by
      apply interior_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact this
  exact hsubset hxCl

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → Topology.P2 A) :
    Topology.P2 (⋃₀ 𝔄) := by
  -- First, extract `P1` and `P3` for every member of `𝔄` from the given `P2`.
  have hP1 : ∀ A, A ∈ 𝔄 → Topology.P1 A := by
    intro A hA_mem
    exact Topology.P2_implies_P1 (hA A hA_mem)
  have hP3 : ∀ A, A ∈ 𝔄 → Topology.P3 A := by
    intro A hA_mem
    exact Topology.P2_implies_P3 (hA A hA_mem)
  -- Use the existing `sUnion` lemmas for `P1` and `P3`.
  have hP1_sUnion : Topology.P1 (⋃₀ 𝔄) := Topology.P1_sUnion hP1
  have hP3_sUnion : Topology.P3 (⋃₀ 𝔄) := Topology.P3_sUnion hP3
  -- Combine them to obtain `P2` for the union.
  exact Topology.P2_of_P1_and_P3 (A := ⋃₀ 𝔄) ⟨hP1_sUnion, hP3_sUnion⟩

theorem P1_closure_iff_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure A) ↔ closure A = closure (interior (closure A)) := by
  simpa [closure_closure] using
    (Topology.P1_iff_closure_eq_closure_interior (A := closure A))

theorem P2_iff_P3_of_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure A = closure (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h := Topology.P2_iff_P3_and_closure_eq_closure_interior (A := A)
  constructor
  · intro hP2
    exact (h.mp hP2).left
  · intro hP3
    exact (h.mpr ⟨hP3, hEq⟩)

theorem P3_closure_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P3_iff_open_of_closed (A := closure A) hClosed)

theorem interior_closure_interior_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  exact interior_mono (closure_mono (interior_subset : (interior A : Set X) ⊆ A))

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  apply closure_mono
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem P2_closure_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h₁ : Topology.P2 (closure A) ↔ Topology.P3 (closure A) := by
    simpa using (Topology.P2_iff_P3_closure (A := A))
  have h₂ : Topology.P3 (closure A) ↔ IsOpen (closure A) := by
    simpa using (Topology.P3_closure_iff_open (A := A))
  exact h₁.trans h₂

theorem P3_of_P1_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpenCl : IsOpen (closure A)) :
    Topology.P3 A := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- From `P1`, obtain membership in `closure (interior A)`.
  have hx_closure_int : x ∈ closure (interior A) := hP1 hxA
  -- `P1` gives an equality of closures.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Transfer membership to `closure A`.
  have hx_closure : x ∈ closure A := by
    simpa [hEq] using hx_closure_int
  -- Since `closure A` is open, its interior is itself.
  have hIntEq : interior (closure A) = closure A := hOpenCl.interior_eq
  -- Conclude the desired membership in the interior.
  simpa [hIntEq] using hx_closure

theorem P123_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  exact ⟨Topology.P1_empty, Topology.P2_empty, Topology.P3_empty⟩

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hne : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  -- First, obtain a point in `interior A` using an existing lemma.
  have hIntA : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hne
  rcases hIntA with ⟨x, hxIntA⟩
  -- Monotonicity of `interior` guarantees the required membership.
  have hxIntCl : x ∈ interior (closure A) := by
    have hsubset : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact hsubset hxIntA
  exact ⟨x, hxIntCl⟩

theorem P1_of_P3_and_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hEq : closure A = closure (interior A)) :
    Topology.P1 A := by
  dsimp [Topology.P3, Topology.P1] at *
  have hint : interior (closure A) ⊆ closure (interior A) := by
    simpa [hEq] using (interior_subset : interior (closure A) ⊆ closure A)
  exact hP3.trans hint

theorem P2_of_P1_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpenCl : IsOpen (closure A)) :
    Topology.P2 A := by
  -- First, upgrade `P1` to `P3` using the openness of `closure A`.
  have hP3 : Topology.P3 A := Topology.P3_of_P1_and_open_closure hP1 hOpenCl
  -- Combine `P1` and the newly obtained `P3` to get `P2`.
  exact Topology.P2_of_P1_and_P3 (A := A) ⟨hP1, hP3⟩

theorem P123_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  exact ⟨Topology.P1_univ, Topology.P2_univ, Topology.P3_univ⟩

theorem P3_of_P2_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hOpenCl : IsOpen (closure A)) :
    Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.P3_of_P1_and_open_closure hP1 hOpenCl

theorem closure_interior_closure_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  ·
    -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆ closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₁ : interior A ⊆ interior (closure (interior A)) := by
      -- `interior A` is open and contained in `closure (interior A)`
      have hsub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      have := interior_mono hsub
      simpa [interior_interior] using this
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    simpa using h₂

theorem P1_of_interior_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior (closure A)))) := by
  simpa using
    (Topology.P1_of_open
        (A := interior (closure (interior (closure A)))) isOpen_interior)

theorem P123_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.P1_of_dense_interior (A := A) hDense,
      Topology.P2_of_dense_interior (A := A) hDense,
      Topology.P3_of_dense_interior (A := A) hDense⟩

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- Since `x ∈ A`, we have `x ∈ closure A`.
  have hxCl : x ∈ closure A := subset_closure hxA
  -- Because `closure A` is open, its interior is itself.
  have hIntEq : interior (closure A) = closure A := hOpenCl.interior_eq
  -- Conclude that `x` lies in the required interior.
  simpa [hIntEq] using hxCl

theorem P1_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure A) := by
  simpa using Topology.P1_of_open (A := closure A) hOpenCl

theorem P1_iff_P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro hP1
    exact Topology.P2_of_P1_and_open_closure (A := A) hP1 hOpenCl
  · intro hP2
    exact Topology.P2_implies_P1 (A := A) hP2

theorem P1_closure_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  have hP1 : Topology.P1 A := Topology.P1_of_open (A := A) hA
  exact Topology.P1_closure_of_P1 (A := A) hP1

theorem interior_closure_interior_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply subset_antisymm
  ·
    -- First inclusion: use the existing general monotonicity lemma.
    simpa using
      (interior_closure_interior_subset (A := closure A))
  ·
    -- Second inclusion: use `interior_maximal` with openness of `interior (closure A)`.
    have hsubset : interior (closure A) ⊆ closure (interior (closure A)) :=
      (subset_closure : (interior (closure A) : Set X) ⊆ closure (interior (closure A)))
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    exact interior_maximal hsubset hOpen

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  intro x hxCl
  have hsubset : (closure A : Set X) ⊆ closure (interior (closure A)) :=
    closure_mono hP3
  exact hsubset hxCl

theorem P1_union_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB_open : IsOpen B) :
    Topology.P1 (A ∪ B) := by
  -- Derive `P1` for the open set `B`.
  have hB : Topology.P1 B := Topology.P1_of_open (A := B) hB_open
  -- Apply the existing union lemma for `P1`.
  exact Topology.P1_union (A := A) (B := B) hA hB

theorem P2_union_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB_open : IsOpen B) :
    Topology.P2 (A ∪ B) := by
  -- Obtain `P2` for the open set `B`.
  have hB : Topology.P2 B := Topology.P2_of_open (A := B) hB_open
  -- Apply the general union lemma for `P2`.
  exact Topology.P2_union (A := A) (B := B) hA hB

theorem P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure A) := by
  simpa using ((Topology.P2_closure_iff_open (A := A)).mpr hOpenCl)

theorem interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hsubset : interior A ⊆ interior (A ∪ B) := by
        apply interior_mono
        exact Set.subset_union_left
      exact hsubset hA
  | inr hB =>
      have hsubset : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        exact Set.subset_union_right
      exact hsubset hB

theorem P3_union_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P3 (A ∪ B) := by
  -- Obtain `P3` for the open set `B`.
  have hB : Topology.P3 B := Topology.P3_of_open (A := B) hB_open
  -- Apply the general union lemma for `P3`.
  exact Topology.P3_union (A := A) (B := B) hA hB

theorem interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A := by
    have hsubset : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    exact (interior_mono hsubset) hx
  have hxB : x ∈ interior B := by
    have hsubset : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact (interior_mono hsubset) hx
  exact ⟨hxA, hxB⟩

theorem closure_interior_eq_of_closed_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = A := by
  have hInt : interior A = A :=
    interior_eq_self_of_closed_of_P3 (A := A) hA hP3
  simpa [hInt, hA.closure_eq]

theorem P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) : Topology.P2 A ↔ Topology.P3 A := by
  -- `P1` yields the key closure equality.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Use the previously established equivalence under this equality.
  simpa using
    (Topology.P2_iff_P3_of_closure_eq_closure_interior (A := A) hEq)

theorem interior_closure_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem P1_iff_P2_and_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Equivalences already established for open sets.
  have h12 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_open (A := A) hA
  have h13 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_open (A := A) hA
  constructor
  · intro hP1
    exact ⟨(h12.mp hP1), (h13.mp hP1)⟩
  · rintro ⟨hP2, _hP3⟩
    exact (h12.mpr hP2)

theorem closure_interior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : closure (interior A) = closure A := by
  simpa using (Topology.closure_eq_closure_interior_of_P2 (A := A) h).symm

theorem P1_iUnion_open {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P1 (⋃ i, A i) := by
  -- Each `A i` is open, hence satisfies `P1`.
  have hP1 : ∀ i, Topology.P1 (A i) := fun i =>
    Topology.P1_of_open (A := A i) (hA i)
  -- Apply the existing `P1`-union lemma.
  exact Topology.P1_iUnion hP1

theorem P3_closure_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P3 (closure A) := by
  simpa using (Topology.P3_closure_iff_open (A := A)).mpr hOpenCl

theorem closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 A) :
    closure A = closure (interior (closure A)) := by
  apply subset_antisymm
  ·
    -- From `P3`, we have `A ⊆ interior (closure A)`.
    have h₁ : (A : Set X) ⊆ interior (closure A) := h
    -- Taking closures yields the desired inclusion.
    simpa using (closure_mono h₁)
  ·
    -- The interior of a set is always contained in the set itself.
    have h₂ : interior (closure A) ⊆ closure A := interior_subset
    -- Taking closures on both sides (and simplifying) gives the reverse inclusion.
    simpa [closure_closure] using (closure_mono h₂)

theorem P3_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, ?_, interior_subset⟩
    intro x hxA
    exact hP3 hxA
  · rintro ⟨U, hU_open, hAU, hUcl⟩
    dsimp [Topology.P3]
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    have hU_in : U ⊆ interior (closure A) :=
      interior_maximal hUcl hU_open
    exact hU_in hxU

theorem isOpen_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (closure (A : Set X))) :
    IsOpen (closure (A : Set X)) := by
  simpa using (Topology.P3_closure_iff_open (A := A)).1 h

theorem P1_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB_open : IsOpen B) :
    Topology.P1 (A ∩ B) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in the closure of `interior A`.
  have hx_clA : x ∈ closure (interior A) := hA hxA
  -- We show `x ∈ closure (interior (A ∩ B))`.
  have hx_cl : x ∈ closure (interior (A ∩ B)) := by
    -- Use the neighbourhood characterisation of closures.
    apply (mem_closure_iff).2
    intro s hs_open hxs
    -- `s ∩ B` is an open neighbourhood of `x`.
    have h_open' : IsOpen (s ∩ B) := hs_open.inter hB_open
    have hx_in' : x ∈ s ∩ B := ⟨hxs, hxB⟩
    -- Since `x ∈ closure (interior A)`, this neighbourhood meets `interior A`.
    have h_nonempty : ((s ∩ B) ∩ interior A).Nonempty :=
      ((mem_closure_iff).1 hx_clA) (s ∩ B) h_open' hx_in'
    -- Extract a witness `y`.
    rcases h_nonempty with ⟨y, ⟨hy_sB, hy_intA⟩⟩
    have hy_s : y ∈ s := hy_sB.1
    have hy_B : y ∈ B := hy_sB.2
    -- `y` lies in `interior A` and in `B`.
    -- Show that `y ∈ interior (A ∩ B)`.
    have hy_intAB : y ∈ interior (A ∩ B) := by
      -- `interior A ∩ B` is an open subset of `A ∩ B` containing `y`.
      have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
        intro z hz
        exact ⟨(interior_subset : interior A ⊆ A) hz.1, hz.2⟩
      have hOpen : IsOpen (interior A ∩ B) := isOpen_interior.inter hB_open
      have hSubInt : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) :=
        interior_maximal hSub hOpen
      exact hSubInt ⟨hy_intA, hy_B⟩
    -- Provide the witness in `s ∩ interior (A ∩ B)`.
    exact ⟨y, ⟨hy_s, hy_intAB⟩⟩
  exact hx_cl

theorem P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2Cl
  have hP3Cl : Topology.P3 (closure A) :=
    Topology.P2_implies_P3 (A := closure A) hP2Cl
  exact Topology.P3_of_closure (A := A) hP3Cl

theorem interior_subset_closure_of_set {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  exact interior_subset.trans subset_closure

theorem P3_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in `interior (closure A)` by `P3`.
  have hxInt : x ∈ interior (closure A) := hA hxA
  -- Consider the open set `U = interior (closure A) ∩ B` that contains `x`.
  have hxU : x ∈ interior (closure A) ∩ B := ⟨hxInt, hxB⟩
  have hU_open : IsOpen (interior (closure A) ∩ B) :=
    isOpen_interior.inter hB_open
  -- Show that `U ⊆ closure (A ∩ B)`.
  have hU_sub : (interior (closure A) ∩ B : Set X) ⊆ closure (A ∩ B) := by
    intro y hyU
    -- Decompose the membership of `y` in `U`.
    have hyB : y ∈ B := hyU.2
    have hyClA : y ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hyU.1
    -- Use the neighbourhood characterization of closure.
    have : y ∈ closure (A ∩ B) := by
      -- Reformulate via `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro s hs_open hy_in_s
      -- `s ∩ B` is an open neighbourhood of `y`.
      have hOpen' : IsOpen (s ∩ B) := hs_open.inter hB_open
      have hy_in' : y ∈ s ∩ B := ⟨hy_in_s, hyB⟩
      -- Since `y ∈ closure A`, this neighbourhood meets `A`.
      have hNonempty : ((s ∩ B) ∩ A).Nonempty :=
        ((mem_closure_iff).1 hyClA) (s ∩ B) hOpen' hy_in'
      -- Extract a witness in `s ∩ (A ∩ B)`.
      rcases hNonempty with ⟨z, ⟨hz_sB, hzA⟩⟩
      exact ⟨z, ⟨hz_sB.1, ⟨hzA, hz_sB.2⟩⟩⟩
    exact this
  -- `U` is an open neighbourhood of `x` contained in `closure (A ∩ B)`,
  -- hence `x ∈ interior (closure (A ∩ B))`.
  have hxTarget :
      x ∈ interior (closure (A ∩ B)) :=
    (interior_maximal hU_sub hU_open) hxU
  exact hxTarget

theorem isOpen_of_closed_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 A) : IsOpen A := by
  exact ((Topology.P2_iff_open_of_closed (A := A) hClosed).1 hP2)

theorem P2_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB_open : IsOpen B) :
    Topology.P2 (A ∩ B) := by
  -- Extract `P1` and `P3` for `A` from the given `P2` assumption.
  have hP1A : Topology.P1 A := Topology.P2_implies_P1 (A := A) hA
  have hP3A : Topology.P3 A := Topology.P2_implies_P3 (A := A) hA
  -- Obtain `P1` and `P3` for the intersection using the existing lemmas.
  have hP1 : Topology.P1 (A ∩ B) :=
    Topology.P1_inter_right_open (A := A) (B := B) hP1A hB_open
  have hP3 : Topology.P3 (A ∩ B) :=
    Topology.P3_inter_right_open (A := A) (B := B) hP3A hB_open
  -- Combine `P1` and `P3` to conclude `P2` for the intersection.
  exact Topology.P2_of_P1_and_P3 (A := A ∩ B) ⟨hP1, hP3⟩

theorem interior_closure_union_eq {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]

theorem closure_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) :
    closure A = closure (interior (closure A)) := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) h
  simpa using Topology.closure_eq_closure_interior_closure_of_P3 (A := A) hP3

theorem P123_of_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) ∧
      Topology.P2 (interior (closure A)) ∧
      Topology.P3 (interior (closure A)) := by
  exact
    ⟨Topology.P1_of_interior_closure (A := A),
      Topology.P2_of_interior_closure (A := A),
      Topology.P3_of_interior_closure (A := A)⟩

theorem P123_closure_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure A) :=
    Topology.P1_of_open_closure (A := A) hOpenCl
  have hP2 : Topology.P2 (closure A) :=
    Topology.P2_of_open_closure (A := A) hOpenCl
  have hP3 : Topology.P3 (closure A) :=
    (Topology.P3_closure_iff_open (A := A)).mpr hOpenCl
  exact ⟨hP1, hP2, hP3⟩

theorem P1_inter_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P1_inter_right_open (A := B) (B := A) hB hA_open)

theorem P2_inter_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P2_inter_right_open (A := B) (B := A) hB hA_open)

theorem P3_inter_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P3_inter_right_open (A := B) (B := A) hB hA_open)

theorem P123_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact ⟨hP1, hP2, hP3⟩

theorem isOpen_of_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) : IsOpen A := by
  exact ((Topology.P3_iff_open_of_closed (A := A) hClosed).mp hP3)

theorem isOpen_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (closure (A : Set X))) :
    IsOpen (closure (A : Set X)) := by
  simpa using ((Topology.P2_closure_iff_open (A := A)).1 h)

theorem P2_union_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P2_union_right_open (A := B) (B := A) hB hA_open)

theorem closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  apply subset_antisymm
  ·
    exact Set.subset_univ _
  ·
    have : (Set.univ : Set X) ⊆ closure A := by
      simpa [hDense] using
        (closure_mono (interior_subset : interior A ⊆ A))
    exact this

theorem interior_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (interior A) ⊆ interior (closure A) := by
  -- Step 1: `interior (interior A)` is contained in `interior (closure (interior A))`.
  have h₁ : interior (interior A) ⊆ interior (closure (interior A)) := by
    simpa [interior_interior] using
      interior_mono
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  -- Step 2: `interior (closure (interior A))` is contained in `interior (closure A)`.
  have h₂ : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Combine the two inclusions.
  exact h₁.trans h₂

theorem eq_empty_of_P1_and_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hIntEmpty : interior A = (∅ : Set X)) :
    A = ∅ := by
  apply Set.Subset.antisymm
  · intro x hxA
    have hxClInt : x ∈ closure (interior A) := hP1 hxA
    have hxClEmpty : x ∈ closure (∅ : Set X) := by
      simpa [hIntEmpty] using hxClInt
    simpa [closure_empty] using hxClEmpty
  · exact Set.empty_subset _

theorem interior_eq_self_of_closed_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  -- A closed set satisfying `P2` is necessarily open.
  have hOpen : IsOpen A := isOpen_of_closed_of_P2 (A := A) hClosed hP2
  -- For an open set, the interior is the set itself.
  simpa using hOpen.interior_eq

theorem P2_of_P1_and_open_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpen : IsOpen (closure (interior A))) :
    Topology.P2 A := by
  dsimp [Topology.P2]   -- we need to show `A ⊆ interior (closure (interior A))`
  intro x hxA
  -- From `P1`, obtain membership in the closure of the interior.
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  -- Since `closure (interior A)` is open, its interior is itself.
  have hIntEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Conclude the desired membership using the equality.
  simpa [hIntEq] using hxCl

theorem P1_union_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  -- Obtain `P1` for the open set `A`.
  have hA : Topology.P1 A := Topology.P1_of_open (A := A) hA_open
  -- Use the existing union lemma for `P1`.
  exact Topology.P1_union (A := A) (B := B) hA hB

theorem interior_inter_eq_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (A ∩ B) = interior A ∩ interior B := by
  apply subset_antisymm
  ·
    -- The forward inclusion holds for arbitrary sets.
    exact interior_inter_subset (A := A) (B := B)
  ·
    -- For the reverse inclusion, use `interior_maximal`.
    have hSub : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro x hx
      exact ⟨(interior_subset : interior A ⊆ A) hx.1,
        (interior_subset : interior B ⊆ B) hx.2⟩
    have hOpen : IsOpen (interior A ∩ interior B) :=
      isOpen_interior.inter isOpen_interior
    exact interior_maximal hSub hOpen

theorem P2_iff_closure_eq_closure_interior_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    Topology.P2 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP2
    exact Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  · intro hEq
    exact Topology.P2_of_P3_and_closure_eq_closure_interior (A := A) hP3 hEq

theorem P1_iff_P2_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  simpa using
    (Topology.P1_iff_P2_of_open (A := interior A) isOpen_interior)

theorem interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  have h :=
    closure_interior_closure_interior_eq (A := A)
  simpa [h]

theorem P3_union_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P3_union_right_open (A := B) (B := A) hB hA_open)

theorem P2_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure A) := by
  intro hP3
  -- Use the equivalence between `P3` and openness for closed sets.
  have hOpen : IsOpen (closure A) :=
    (Topology.P3_closure_iff_open (A := A)).1 hP3
  -- Translate openness back to `P2` via the corresponding equivalence.
  exact (Topology.P2_closure_iff_open (A := A)).2 hOpen

theorem P2_of_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P2 A := by
  -- For closed sets, `P2` and `P3` are equivalent.
  have hEquiv : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_closed (A := A) hClosed
  -- Apply the equivalence to turn the given `P3` into `P2`.
  exact (hEquiv.mpr hP3)

theorem interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  -- Step 1: send `x` into `interior (closure A)` via monotonicity of `interior`.
  have hx₁ : x ∈ interior (closure A) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx
  -- Step 2: every set is contained in its closure.
  have hsubset : (interior (closure A) : Set X) ⊆ closure (interior (closure A)) :=
    subset_closure
  exact hsubset hx₁

theorem P2_iUnion_open {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P2 (⋃ i, A i) := by
  -- Each `A i` is open, hence satisfies `P2`.
  have hP2 : ∀ i, Topology.P2 (A i) := fun i =>
    Topology.P2_of_open (A := A i) (hA i)
  -- Apply the existing union lemma for `P2`.
  exact Topology.P2_iUnion hP2

theorem closure_interior_closure_interior_closure_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (closure_interior_closure_interior_eq (A := closure A))

theorem closure_interior_iInter_subset {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (interior (⋂ i, A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- For every `i`, show `x ∈ closure (interior (A i))`.
  have hxAll : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- Use monotonicity of `interior` and `closure` together with the basic set inclusion.
    have hsubset : closure (interior (⋂ j, A j)) ⊆ closure (interior (A i)) := by
      apply closure_mono
      apply interior_mono
      exact Set.iInter_subset (fun j => A j) i
    exact hsubset hx
  -- Assemble the witnesses into the intersection.
  exact Set.mem_iInter.2 hxAll

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem P1_iff_P3_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P1_iff_P3_of_open (A := interior A) hOpen)

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem interior_union_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = interior A ∪ interior B := by
  have hA_eq : interior A = A := hA.interior_eq
  have hB_eq : interior B = B := hB.interior_eq
  have hUnion_eq : interior (A ∪ B) = A ∪ B := (hA.union hB).interior_eq
  simpa [hA_eq, hB_eq, hUnion_eq]

theorem closure_iUnion_closure_eq {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (⋃ i, closure (A i)) = closure (⋃ i, A i) := by
  apply subset_antisymm
  ·
    -- `closure (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i)`
    have hSub : (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i) := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      have hCl : closure (A i) ⊆ closure (⋃ j, A j) :=
        closure_mono (Set.subset_iUnion _ _)
      exact hCl hx_i
    have : closure (⋃ i, closure (A i)) ⊆ closure (closure (⋃ i, A i)) :=
      closure_mono hSub
    simpa [closure_closure] using this
  ·
    -- `closure (⋃ i, A i) ⊆ closure (⋃ i, closure (A i))`
    have hSub : (⋃ i, A i) ⊆ ⋃ i, closure (A i) := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      exact Set.mem_iUnion.2 ⟨i, subset_closure hx_i⟩
    exact closure_mono hSub

theorem P2_iff_P3_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) ↔ Topology.P3 (interior A) := by
  simpa using
    (Topology.P2_iff_P3_of_open (A := interior A) isOpen_interior)

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  have h : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  simpa [interior_interior] using (interior_mono h)

theorem P2_prod_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P2 (Set.prod A B) := by
  have hOpen : IsOpen (Set.prod A B) := hA.prod hB
  simpa using (Topology.P2_of_open (A := Set.prod A B) hOpen)

theorem P1_prod_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (Set.prod A B) := by
  have hOpen : IsOpen (Set.prod A B) := hA.prod hB
  simpa using Topology.P1_of_open (A := Set.prod A B) hOpen

theorem P3_prod_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P3 (Set.prod A B) := by
  have hOpen : IsOpen (Set.prod A B) := hA.prod hB
  simpa using (Topology.P3_of_open (A := Set.prod A B) hOpen)

theorem closure_iInter_interior_subset {X ι : Type*} [TopologicalSpace X]
    {A : ι → Set X} :
    closure (⋂ i, interior (A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- For every `i`, show that `x` belongs to `closure (interior (A i))`.
  have hforall : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- The intersection is contained in each `interior (A i)`.
    have hsubset :
        (⋂ j, interior (A j)) ⊆ interior (A i) :=
      Set.iInter_subset (fun j : ι => interior (A j)) i
    -- Monotonicity of `closure` transfers membership.
    exact (closure_mono hsubset) hx
  -- Collect the witnesses into the intersection.
  exact Set.mem_iInter.2 hforall

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) :
    Topology.P3 (A ×ˢ B) := by
  dsimp [Topology.P3] at *
  intro p hp
  -- Decompose `p` and obtain coordinate membership.
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P3` to each coordinate.
  have hIntA : p.1 ∈ interior (closure A) := hA hpA
  have hIntB : p.2 ∈ interior (closure B) := hB hpB
  -- The point `p` lies in the product of the two interiors.
  have hMemProd :
      p ∈ interior (closure A) ×ˢ interior (closure B) := by
    exact ⟨hIntA, hIntB⟩
  -- This rectangle is open.
  have hOpenProd :
      IsOpen (interior (closure A) ×ˢ interior (closure B)) :=
    (isOpen_interior).prod isOpen_interior
  -- Show the rectangle is contained in `closure (A ×ˢ B)`.
  have hSubProd :
      (interior (closure A) ×ˢ interior (closure B)) ⊆
        closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    have hqA_cl : q.1 ∈ closure A := (interior_subset) hqA
    have hqB_cl : q.2 ∈ closure B := (interior_subset) hqB
    have hqIn : q ∈ closure A ×ˢ closure B := ⟨hqA_cl, hqB_cl⟩
    simpa [closure_prod_eq] using hqIn
  -- Use `interior_maximal` to upgrade membership.
  have hSubInterior :
      (interior (closure A) ×ˢ interior (closure B)) ⊆
        interior (closure (A ×ˢ B)) :=
    interior_maximal hSubProd hOpenProd
  exact hSubInterior hMemProd

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (A ×ˢ B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro p hpAB
  rcases hpAB with ⟨hpA, hpB⟩
  -- Send each coordinate into the corresponding closure.
  have hclA : p.1 ∈ closure (interior A) := hA hpA
  have hclB : p.2 ∈ closure (interior B) := hB hpB
  -- Combine them to obtain membership in the product of closures.
  have hProd : p ∈ closure (interior A) ×ˢ closure (interior B) := ⟨hclA, hclB⟩
  -- Rewrite the goal using `closure_prod_eq`.
  have hProdIn :
      p ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [closure_prod_eq] using hProd
  -- Show that this closure is contained in the desired one.
  have hSubset :
      closure ((interior A) ×ˢ (interior B)) ⊆
        closure (interior (A ×ˢ B)) := by
    -- First, establish the inclusion on the underlying sets.
    have hInnerSub :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆
          interior (A ×ˢ B) := by
      -- `interior A ×ˢ interior B` is open and contained in `A ×ˢ B`.
      have hOpen : IsOpen (interior A ×ˢ interior B) :=
        (isOpen_interior).prod isOpen_interior
      have hSub : (interior A ×ˢ interior B : Set _) ⊆ A ×ˢ B := by
        intro q hq
        exact ⟨(interior_subset hq.1), (interior_subset hq.2)⟩
      exact interior_maximal hSub hOpen
    -- Taking closures preserves inclusions.
    exact closure_mono hInnerSub
  exact hSubset hProdIn

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) :
    Topology.P2 (A ×ˢ B) := by
  -- Obtain `P1` and `P3` for each factor from the given `P2` assumptions.
  have hP1A : Topology.P1 A := Topology.P2_implies_P1 (A := A) hA
  have hP1B : Topology.P1 B := Topology.P2_implies_P1 (A := B) hB
  have hP3A : Topology.P3 A := Topology.P2_implies_P3 (A := A) hA
  have hP3B : Topology.P3 B := Topology.P2_implies_P3 (A := B) hB
  -- Combine the `P1` and `P3` properties using the existing product lemmas.
  have hP1Prod : Topology.P1 (A ×ˢ B) := Topology.P1_prod hP1A hP1B
  have hP3Prod : Topology.P3 (A ×ˢ B) := Topology.P3_prod hP3A hP3B
  -- Conclude `P2` for the product using `P1` and `P3`.
  exact Topology.P2_of_P1_and_P3 (A := A ×ˢ B) ⟨hP1Prod, hP3Prod⟩

theorem P2_closure_interior_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P2_iff_open_of_closed (A := closure (interior A)) hClosed)

theorem P2_prod_right_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB_open : IsOpen B) :
    Topology.P2 (A ×ˢ B) := by
  have hB : Topology.P2 B := Topology.P2_of_open (A := B) hB_open
  exact Topology.P2_prod (A := A) (B := B) hA hB

theorem P2_prod_left_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hB : Topology.P2 B) :
    Topology.P2 (A ×ˢ B) := by
  -- The open set `A` automatically satisfies `P2`.
  have hA : Topology.P2 A := Topology.P2_of_open (A := A) hA_open
  -- Apply the existing product lemma for `P2`.
  exact Topology.P2_prod (A := A) (B := B) hA hB

theorem P3_prod_right_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P3 (A ×ˢ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro p hpAB
  -- Decompose the point `p` into its coordinates.
  rcases hpAB with ⟨hpA, hpB⟩
  -- Apply `P3` to the first coordinate.
  have hIntA : p.1 ∈ interior (closure A) := hA hpA
  -- Form an open rectangle containing `p`.
  have hMem : p ∈ interior (closure A) ×ˢ B := ⟨hIntA, hpB⟩
  have hOpen : IsOpen (interior (closure A) ×ˢ B) :=
    (isOpen_interior).prod hB_open
  -- Show that the rectangle is contained in `closure (A ×ˢ B)`.
  have hSub :
      (interior (closure A) ×ˢ B : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    have hqA_cl : q.1 ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hqA
    have hqB_cl : q.2 ∈ closure B := subset_closure hqB
    have : q ∈ closure A ×ˢ closure B := ⟨hqA_cl, hqB_cl⟩
    simpa [closure_prod_eq] using this
  -- Upgrade membership to the desired interior via `interior_maximal`.
  have hSubInt :
      (interior (closure A) ×ˢ B : Set _) ⊆ interior (closure (A ×ˢ B)) :=
    interior_maximal hSub hOpen
  exact hSubInt hMem

theorem P1_prod_right_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB_open : IsOpen B) :
    Topology.P1 (A ×ˢ B) := by
  -- Translate the openness of `B` into the `P1` property.
  have hB : Topology.P1 B := Topology.P1_of_open (A := B) hB_open
  -- Conclude using the general product lemma for `P1`.
  exact Topology.P1_prod hA hB

theorem P1_prod_left_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ×ˢ B) := by
  -- `A` is open, hence satisfies `P1`.
  have hA : Topology.P1 A := Topology.P1_of_open (A := A) hA_open
  -- Apply the existing product lemma for `P1`.
  exact Topology.P1_prod hA hB

theorem interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simpa [closure_empty] using interior_empty

theorem P3_prod_left_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ×ˢ B) := by
  dsimp [Topology.P3] at hB ⊢
  intro p hpAB
  rcases hpAB with ⟨hpA, hpB⟩
  -- Apply `P3` to obtain interior membership for the second coordinate.
  have hIntB : p.2 ∈ interior (closure B) := hB hpB
  -- Form an open rectangle `A ×ˢ interior (closure B)` containing `p`.
  have hMem : p ∈ A ×ˢ interior (closure B) := ⟨hpA, hIntB⟩
  have hOpenRect : IsOpen (A ×ˢ interior (closure B)) :=
    hA_open.prod isOpen_interior
  -- Show that this rectangle is contained in `closure (A ×ˢ B)`.
  have hSub : (A ×ˢ interior (closure B) : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqA, hqBInt⟩
    have hqA_cl : q.1 ∈ closure A := subset_closure hqA
    have hqB_cl : q.2 ∈ closure B :=
      (interior_subset : interior (closure B) ⊆ closure B) hqBInt
    have : q ∈ closure A ×ˢ closure B := ⟨hqA_cl, hqB_cl⟩
    simpa [closure_prod_eq] using this
  -- Use `interior_maximal` to upgrade to interior membership.
  have hSubInt :
      (A ×ˢ interior (closure B) : Set _) ⊆ interior (closure (A ×ˢ B)) :=
    interior_maximal hSub hOpenRect
  exact hSubInt hMem

theorem P123_prod_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B) := by
  exact
    ⟨Topology.P1_prod_open (A := A) (B := B) hA hB,
      Topology.P2_prod_open (A := A) (B := B) hA hB,
      Topology.P3_prod_open (A := A) (B := B) hA hB⟩

theorem interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  -- First apply the idempotence lemma to the inner expression.
  have h₁ :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
    simpa using
      (interior_closure_interior_closure_eq
        (A := interior (closure A)))
  -- A second application collapses one more layer.
  have h₂ :
      interior (closure (interior (closure A))) =
        interior (closure A) :=
    interior_closure_interior_closure_eq (A := A)
  -- Combine the two equalities to obtain the desired result.
  simpa [h₂] using h₁

theorem interior_closure_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA.closure_eq]

theorem interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  exact subset_closure

theorem eq_empty_of_P2_and_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hIntEmpty : interior A = (∅ : Set X)) :
    A = ∅ := by
  apply Set.Subset.antisymm
  · intro x hxA
    have hxInner : x ∈ interior (closure (interior A)) := hP2 hxA
    simpa [hIntEmpty, closure_empty, interior_empty] using hxInner
  · exact Set.empty_subset _

theorem P123_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A)
    (hB : Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B) :
    Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B) := by
  rcases hA with ⟨hP1A, hP2A, hP3A⟩
  rcases hB with ⟨hP1B, hP2B, hP3B⟩
  have hP1Prod : Topology.P1 (A ×ˢ B) := Topology.P1_prod hP1A hP1B
  have hP2Prod : Topology.P2 (A ×ˢ B) := Topology.P2_prod hP2A hP2B
  have hP3Prod : Topology.P3 (A ×ˢ B) := Topology.P3_prod hP3A hP3B
  exact ⟨hP1Prod, hP2Prod, hP3Prod⟩

theorem not_P2_of_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntEmpty : interior A = (∅ : Set X)) (hne : A.Nonempty) :
    ¬ Topology.P2 A := by
  intro hP2
  have hInt : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P2 (A := A) hP2 hne
  simpa [hIntEmpty] using hInt

theorem interior_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure A) := by
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem P3_of_P3_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (h : Topology.P3 (A ×ˢ B)) :
    Topology.P3 A := by
  dsimp [Topology.P3] at h ⊢
  intro x hxA
  rcases hB with ⟨y, hyB⟩
  have hxy_prod : (x, y) ∈ A ×ˢ B := by
    exact And.intro hxA hyB
  have hxy_int : (x, y) ∈ interior (closure (A ×ˢ B)) := h hxy_prod
  have hxy_int' : (x, y) ∈ interior (closure A ×ˢ closure B) := by
    simpa [closure_prod_eq] using hxy_int
  have hxy_int'' :
      (x, y) ∈ interior (closure A) ×ˢ interior (closure B) := by
    simpa [interior_prod_eq] using hxy_int'
  exact hxy_int''.1

theorem P1_of_P1_prod_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (h : Topology.P1 (A ×ˢ B)) :
    Topology.P1 A := by
  dsimp [Topology.P1] at h ⊢
  intro x hxA
  rcases hB with ⟨y, hyB⟩
  -- Form the point in the product set.
  have hxy : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Use `P1` for the product to obtain closure membership.
  have hcl₁ : (x, y) ∈ closure (interior (A ×ˢ B)) := h hxy
  -- Rewrite the interior of a product as the product of interiors.
  have hcl₂ :
      (x, y) ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [interior_prod_eq] using hcl₁
  -- Rewrite the closure of a product as the product of closures.
  have hcl₃ :
      (x, y) ∈ closure (interior A) ×ˢ closure (interior B) := by
    simpa [closure_prod_eq] using hcl₂
  -- Extract the first coordinate to conclude.
  exact hcl₃.1

theorem P3_of_P3_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (h : Topology.P3 (A ×ˢ B)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at h ⊢
  intro y hyB
  rcases hA with ⟨x, hxA⟩
  -- Form the point in the product set.
  have hxy_prod : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P3` for the product.
  have hxy_int : (x, y) ∈ interior (closure (A ×ˢ B)) := h hxy_prod
  -- Rewrite using properties of `closure` and `interior` for products.
  have hxy_int' : (x, y) ∈ interior (closure A ×ˢ closure B) := by
    simpa [closure_prod_eq] using hxy_int
  have hxy_int'' : (x, y) ∈ interior (closure A) ×ˢ interior (closure B) := by
    simpa [interior_prod_eq] using hxy_int'
  -- Extract the second coordinate.
  exact hxy_int''.2

theorem interior_closure_prod_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    interior (closure (A ×ˢ B)) = interior (closure A ×ˢ closure B) := by
  simpa [closure_prod_eq]

theorem closure_interior_prod_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    closure (interior A) ×ˢ closure (interior B) ⊆
      closure (interior (A ×ˢ B)) := by
  intro p hp
  -- Step 1: rewrite the hypothesis using `closure_prod_eq`.
  have h₁ : (p : X × Y) ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [closure_prod_eq] using hp
  -- Step 2: show the needed containment between the closures.
  have hsubset :
      (closure ((interior A) ×ˢ (interior B)) : Set (X × Y)) ⊆
        closure (interior (A ×ˢ B)) := by
    apply closure_mono
    -- Establish the inclusion on the underlying sets via `interior_maximal`.
    have hInnerSub :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
      -- `interior A ×ˢ interior B` is an open subset of `A ×ˢ B`.
      have hOpen : IsOpen (interior A ×ˢ interior B) :=
        (isOpen_interior).prod isOpen_interior
      have hSub : (interior A ×ˢ interior B : Set _) ⊆ A ×ˢ B := by
        intro q hq
        exact ⟨(interior_subset hq.1), (interior_subset hq.2)⟩
      exact interior_maximal hSub hOpen
    exact hInnerSub
  -- Step 3: conclude by applying the inclusion to the membership obtained in Step 1.
  exact hsubset h₁

theorem P2_of_P2_prod_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P2 A := by
  dsimp [Topology.P2] at hP2 ⊢
  intro x hxA
  rcases hB with ⟨y, hyB⟩
  -- Form the point in the product set.
  have hxy_prod : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P2` for the product.
  have hmem : (x, y) ∈ interior (closure (interior (A ×ˢ B))) :=
    hP2 hxy_prod
  -- Rewrite `interior (A ×ˢ B)` via `interior_prod_eq`.
  have hmem₁ :
      (x, y) ∈ interior (closure ((interior A) ×ˢ (interior B))) := by
    simpa [interior_prod_eq] using hmem
  -- Use the lemma `interior_closure_prod_eq` to split the closure of a product.
  have hmem₂ :
      (x, y) ∈ interior (closure (interior A) ×ˢ closure (interior B)) := by
    simpa [interior_closure_prod_eq
            (A := interior A) (B := interior B)] using hmem₁
  -- Apply `interior_prod_eq` once more to separate the coordinates.
  have hmem₃ :
      (x, y) ∈ interior (closure (interior A)) ×ˢ
        interior (closure (interior B)) := by
    simpa [interior_prod_eq] using hmem₂
  -- Extract the first coordinate to conclude `P2` for `A`.
  exact hmem₃.1

theorem P2_of_P2_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P2 B := by
  dsimp [Topology.P2] at hP2 ⊢
  intro y hyB
  rcases hA with ⟨x, hxA⟩
  -- Form the point `(x, y) ∈ A ×ˢ B`.
  have hxy : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P2` for the product.
  have hxy_int : (x, y) ∈ interior (closure (interior (A ×ˢ B))) := hP2 hxy
  -- Rewrite `interior (A ×ˢ B)` via `interior_prod_eq`.
  have hxy_int₁ :
      (x, y) ∈ interior (closure ((interior A) ×ˢ (interior B))) := by
    simpa [interior_prod_eq] using hxy_int
  -- Use the lemma `interior_closure_prod_eq` to split the closure of a product.
  have hxy_int₂ :
      (x, y) ∈ interior (closure (interior A) ×ˢ closure (interior B)) := by
    simpa [interior_closure_prod_eq
            (A := interior A) (B := interior B)] using hxy_int₁
  -- Apply `interior_prod_eq` once more to separate the coordinates.
  have hxy_int₃ :
      (x, y) ∈ interior (closure (interior A)) ×ˢ
        interior (closure (interior B)) := by
    simpa [interior_prod_eq] using hxy_int₂
  -- Extract the second coordinate to conclude `P2` for `B`.
  exact hxy_int₃.2

theorem P1_of_P1_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (h : Topology.P1 (A ×ˢ B)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at h ⊢
  intro y hyB
  rcases hA with ⟨x, hxA⟩
  -- Form the point `(x, y) ∈ A ×ˢ B`.
  have hxy_prod : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P1` for the product.
  have hxy_closure₁ :
      (x, y) ∈ closure (interior (A ×ˢ B)) := h hxy_prod
  -- Rewrite `interior (A ×ˢ B)` via `interior_prod_eq`.
  have hxy_closure₂ :
      (x, y) ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [interior_prod_eq] using hxy_closure₁
  -- Rewrite the closure of a product via `closure_prod_eq`.
  have hxy_closure₃ :
      (x, y) ∈ closure (interior A) ×ˢ closure (interior B) := by
    simpa [closure_prod_eq] using hxy_closure₂
  -- Extract the second coordinate to conclude `P1` for `B`.
  exact hxy_closure₃.2

theorem P3_closure_interior_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P3_iff_open_of_closed (A := closure (interior A)) hClosed)

theorem P2_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty) (hB : B.Nonempty) :
    Topology.P2 (A ×ˢ B) ↔ (Topology.P2 A ∧ Topology.P2 B) := by
  constructor
  · intro hP2Prod
    have hP2A : Topology.P2 A :=
      Topology.P2_of_P2_prod_left (A := A) (B := B) hB hP2Prod
    have hP2B : Topology.P2 B :=
      Topology.P2_of_P2_prod_right (A := A) (B := B) hA hP2Prod
    exact ⟨hP2A, hP2B⟩
  · rintro ⟨hP2A, hP2B⟩
    exact Topology.P2_prod (A := A) (B := B) hP2A hP2B

theorem P3_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty) (hB : B.Nonempty) :
    Topology.P3 (A ×ˢ B) ↔ (Topology.P3 A ∧ Topology.P3 B) := by
  constructor
  · intro hP3Prod
    have hP3A : Topology.P3 A :=
      Topology.P3_of_P3_prod_left (A := A) (B := B) hB hP3Prod
    have hP3B : Topology.P3 B :=
      Topology.P3_of_P3_prod_right (A := A) (B := B) hA hP3Prod
    exact ⟨hP3A, hP3B⟩
  · rintro ⟨hP3A, hP3B⟩
    exact Topology.P3_prod hP3A hP3B

theorem interior_inter_eq_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  simpa using (hA.inter hB).interior_eq

theorem closure_iInter_subset_iInter_closure
    {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (⋂ i, A i) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- Show that `x ∈ closure (A i)` for every `i`.
  have hx_all : ∀ i, x ∈ closure (A i) := by
    intro i
    -- `⋂ i, A i` is contained in `A i`.
    have hsub : (⋂ j, A j : Set X) ⊆ A i :=
      Set.iInter_subset (fun j => A j) i
    -- Monotonicity of `closure` upgrades the inclusion.
    have hcl : closure (⋂ j, A j) ⊆ closure (A i) := closure_mono hsub
    exact hcl hx
  -- Collect the memberships into the intersection.
  exact Set.mem_iInter.2 hx_all

theorem P1_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty) (hB : B.Nonempty) :
    Topology.P1 (A ×ˢ B) ↔ (Topology.P1 A ∧ Topology.P1 B) := by
  constructor
  · intro hP1Prod
    have hP1A : Topology.P1 A :=
      Topology.P1_of_P1_prod_left (A := A) (B := B) hB hP1Prod
    have hP1B : Topology.P1 B :=
      Topology.P1_of_P1_prod_right (A := A) (B := B) hA hP1Prod
    exact ⟨hP1A, hP1B⟩
  · rintro ⟨hP1A, hP1B⟩
    exact Topology.P1_prod hP1A hP1B

theorem P1_of_P2_prod_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P1 A := by
  -- First, extract `P2` for `A` from the product assumption.
  have hP2A : Topology.P2 A :=
    Topology.P2_of_P2_prod_left (A := A) (B := B) hB hP2
  -- Since `P2` implies `P1`, we obtain the desired result.
  exact Topology.P2_implies_P1 (A := A) hP2A

theorem P1_iff_P2_and_P3_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔
      (Topology.P2 (interior A) ∧ Topology.P3 (interior A)) := by
  simpa using
    (Topology.P1_iff_P2_and_P3_of_open (A := interior A) isOpen_interior)

theorem P123_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧
      Topology.P2 (interior A) ∧
      Topology.P3 (interior A) := by
  exact
    ⟨Topology.P1_of_interior (A := A),
      Topology.P2_of_interior (A := A),
      Topology.P3_of_interior (A := A)⟩

theorem P2_iff_P3_and_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔
      (Topology.P3 A ∧ interior (closure A) = interior (closure (interior A))) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
    have hEq : interior (closure A) = interior (closure (interior A)) :=
      interior_closure_eq_closure_interior_of_P2 (A := A) hP2
    exact And.intro hP3 hEq
  · rintro ⟨hP3, hEq⟩
    dsimp [Topology.P2]
    intro x hxA
    have hxInt : x ∈ interior (closure A) := hP3 hxA
    simpa [hEq] using hxInt

theorem interior_closure_prod_eq_prod_interiors {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    interior (closure (A ×ˢ B)) = interior (closure A) ×ˢ interior (closure B) := by
  simpa [interior_prod_eq] using
    (interior_closure_prod_eq (A := A) (B := B))

theorem P1_of_P2_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro y hyB
  -- Pick an element `x ∈ A` to form the product point `(x, y)`.
  rcases hA with ⟨x, hxA⟩
  have hxy_prod : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P2` for the product to obtain interior membership.
  have hxy_int :
      (x, y) ∈ interior (closure (interior (A ×ˢ B))) := hP2 hxy_prod
  -- The interior is contained in the closure of the same set.
  have hxy_closure₁ :
      (x, y) ∈ closure (interior (A ×ˢ B)) :=
    (interior_subset : interior (closure (interior (A ×ˢ B)))
        ⊆ closure (interior (A ×ˢ B))) hxy_int
  -- Rewrite `interior (A ×ˢ B)` via `interior_prod_eq`.
  have hxy_closure₂ :
      (x, y) ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [interior_prod_eq] using hxy_closure₁
  -- Rewrite the closure of a product via `closure_prod_eq`.
  have hxy_closure₃ :
      (x, y) ∈ closure (interior A) ×ˢ closure (interior B) := by
    simpa [closure_prod_eq] using hxy_closure₂
  -- Extract the second coordinate to conclude `y ∈ closure (interior B)`.
  exact hxy_closure₃.2

theorem P3_of_P2_prod_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P3 A := by
  -- Upgrade the product hypothesis from `P2` to `P3`.
  have hP3Prod : Topology.P3 (A ×ˢ B) :=
    Topology.P2_implies_P3 (A := A ×ˢ B) hP2
  -- Use the existing projection lemma for `P3`.
  exact Topology.P3_of_P3_prod_left (A := A) (B := B) hB hP3Prod

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  intro x hx
  have hcl : closure (interior A) ⊆ closure (interior B) := by
    apply closure_mono
    exact interior_mono hAB
  exact (interior_mono hcl) hx

theorem P3_of_P2_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P3 B := by
  -- First, upgrade the product assumption from `P2` to `P3`.
  have hP3Prod : Topology.P3 (A ×ˢ B) :=
    Topology.P2_implies_P3 (A := A ×ˢ B) hP2
  -- Use the existing projection lemma for `P3` to obtain the result.
  exact Topology.P3_of_P3_prod_right (A := A) (B := B) hA hP3Prod

theorem interior_nonempty_iff_nonempty_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    (interior A).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, (interior_subset : interior A ⊆ A) hxInt⟩
  · intro hA
    exact Topology.interior_nonempty_of_P1 (A := A) hP1 hA

theorem interior_nonempty_iff_nonempty_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    (interior A).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, (interior_subset : interior A ⊆ A) hxInt⟩
  · intro hA
    exact Topology.interior_nonempty_of_P2 (A := A) hP2 hA

theorem interior_closure_nonempty_iff_nonempty_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    (interior (closure A)).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hInt
    -- `closure A` is nonempty because its interior is.
    have hCl : (closure A).Nonempty := by
      rcases hInt with ⟨x, hx⟩
      exact ⟨x, (interior_subset : interior (closure A) ⊆ closure A) hx⟩
    -- Either `A` is nonempty or we derive a contradiction.
    by_cases hA : A.Nonempty
    · exact hA
    · -- If `A` were empty, its closure would be empty, contradicting `hCl`.
      have hAeq : (A : Set X) = ∅ :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have hFalse : False := by
        have : (∅ : Set X).Nonempty := by
          simpa [hAeq, closure_empty] using hCl
        rcases this with ⟨x, hx⟩
        exact hx
      exact (False.elim hFalse)
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P3 (A := A) hP3 hA

theorem Set.nonempty_univ {α : Type*} [Nonempty α] :
    (Set.univ : Set α).Nonempty := by
  classical
  rcases ‹Nonempty α› with ⟨a⟩
  exact ⟨a, by simp⟩

theorem closure_interior_prod_eq_prod_closure_interiors
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    closure ((interior A) ×ˢ (interior B)) =
      closure (interior A) ×ˢ closure (interior B) := by
  simpa using
    (closure_prod_eq :
      closure ((interior A) ×ˢ (interior B)) =
        closure (interior A) ×ˢ closure (interior B))

theorem P2_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P2 (closure (A : Set X)) := by
  simpa [hDense] using (Topology.P2_univ (X := X))

theorem P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P2 A := by
  -- `P1` yields an equality of closures.
  have hEq : closure (interior A) = closure A := by
    simpa using
      (Topology.closure_eq_closure_interior_of_P1 (A := A) hP1).symm
  -- Combine with the density assumption to make `closure (interior A)` the whole space.
  have hDenseInt : closure (interior A) = (Set.univ : Set X) := by
    simpa [hEq] using hDense
  -- Invoke the existing lemma that turns this density into `P2`.
  exact Topology.P2_of_dense_interior (A := A) hDenseInt

theorem closure_eq_univ_of_interior_closure_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro x _
    have hxInt : x ∈ interior (closure (A : Set X)) := by
      simpa [h] using Set.mem_univ x
    exact (interior_subset : interior (closure (A : Set X)) ⊆ closure (A : Set X)) hxInt

theorem P1_iff_P2_of_open_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior A))) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro hP1
    exact Topology.P2_of_P1_and_open_closure_interior (A := A) hP1 hOpen
  · intro hP2
    exact Topology.P2_implies_P1 (A := A) hP2

theorem closure_iInter_eq_iInter {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsClosed (A i)) :
    closure (⋂ i, A i) = ⋂ i, A i := by
  have hClosed : IsClosed (⋂ i, A i) := by
    simpa using isClosed_iInter hA
  simpa using hClosed.closure_eq

theorem interior_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    interior A ⊆ interior (closure (interior A)) := by
  dsimp [Topology.P2] at hP2
  intro x hxIntA
  exact hP2 ((interior_subset : interior A ⊆ A) hxIntA)

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  have h₁ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_closure_interior_subset (A := A)
  have h₂ : interior (closure A) ⊆ closure A := interior_subset
  exact h₁.trans h₂

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    interior (closure A) = (Set.univ : Set X) := by
  simpa [hDense, interior_univ]

theorem P3_of_interior_closure_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using hx_univ

theorem closure_inter_subset_closure_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  have hB : x ∈ closure B :=
    (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact ⟨hA, hB⟩

theorem interior_closure_inter_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : x ∈ interior (closure A) := by
    have hsubset : (closure A ∩ closure B : Set X) ⊆ closure A :=
      Set.inter_subset_left
    exact (interior_mono hsubset) hx
  have hB : x ∈ interior (closure B) := by
    have hsubset : (closure A ∩ closure B : Set X) ⊆ closure B :=
      Set.inter_subset_right
    exact (interior_mono hsubset) hx
  exact ⟨hA, hB⟩

theorem not_P1_of_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntEmpty : interior A = (∅ : Set X)) (hne : A.Nonempty) :
    ¬ Topology.P1 A := by
  intro hP1
  have hIntNonempty : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hne
  simpa [hIntEmpty] using hIntNonempty

theorem P123_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty) (hB : B.Nonempty) :
    (Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B)) ↔
      ((Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ∧
        (Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B)) := by
  constructor
  · -- From the product triple, deduce triples for each factor.
    rintro ⟨hP1Prod, hP2Prod, hP3Prod⟩
    -- Extract the `P1` properties.
    have hP1Factors :=
      (Topology.P1_prod_iff (A := A) (B := B) hA hB).1 hP1Prod
    rcases hP1Factors with ⟨hP1A, hP1B⟩
    -- Extract the `P2` properties.
    have hP2Factors :=
      (Topology.P2_prod_iff (A := A) (B := B) hA hB).1 hP2Prod
    rcases hP2Factors with ⟨hP2A, hP2B⟩
    -- Extract the `P3` properties.
    have hP3Factors :=
      (Topology.P3_prod_iff (A := A) (B := B) hA hB).1 hP3Prod
    rcases hP3Factors with ⟨hP3A, hP3B⟩
    -- Assemble the result.
    exact ⟨⟨hP1A, hP2A, hP3A⟩, ⟨hP1B, hP2B, hP3B⟩⟩
  · -- From triples for the factors, build the product triple.
    rintro ⟨hTripleA, hTripleB⟩
    exact
      Topology.P123_prod (A := A) (B := B) hTripleA hTripleB

theorem P123_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i) ∧ Topology.P2 (A i) ∧ Topology.P3 (A i)) :
    Topology.P1 (⋃ i, A i) ∧ Topology.P2 (⋃ i, A i) ∧ Topology.P3 (⋃ i, A i) := by
  -- Extract each component property for every `A i`.
  have hP1 : ∀ i, Topology.P1 (A i) := fun i => (hA i).1
  have hP2 : ∀ i, Topology.P2 (A i) := fun i => (hA i).2.1
  have hP3 : ∀ i, Topology.P3 (A i) := fun i => (hA i).2.2
  -- Apply the existing `iUnion` lemmas for each property.
  have hP1Union : Topology.P1 (⋃ i, A i) := Topology.P1_iUnion hP1
  have hP3Union : Topology.P3 (⋃ i, A i) := Topology.P3_iUnion hP3
  have hP2Union : Topology.P2 (⋃ i, A i) := Topology.P2_iUnion hP2
  exact ⟨hP1Union, hP2Union, hP3Union⟩

theorem interior_closure_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    (interior (closure A)).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hInt
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · -- If `A` is empty, its closure and hence the given interior are empty,
      -- contradicting `hInt`.
      have hAeq : (A : Set X) = ∅ :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have : (interior (∅ : Set X)).Nonempty := by
        simpa [hAeq, closure_empty] using hInt
      simpa [interior_empty] using this
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P2 (A := A) hP2 hA

theorem interior_closure_nonempty_iff_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    (interior (closure A)).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hInt
    by_contra hA
    have hAeq : (A : Set X) = ∅ :=
      (Set.not_nonempty_iff_eq_empty).1 hA
    rcases hInt with ⟨x, hxInt⟩
    have hxCl : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hxInt
    have : x ∈ (∅ : Set X) := by
      simpa [hAeq, closure_empty] using hxCl
    exact (Set.not_mem_empty x) this
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P1 (A := A) hP1 hA

theorem P1_of_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P1 A := by
  -- A closed set satisfying `P3` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_closed_of_P3 (A := A) hClosed hP3
  -- Every open set satisfies `P1`.
  exact Topology.P1_of_open (A := A) hOpen



theorem closure_interior_subset_closure_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (A) := by
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem interior_closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  intro x hx
  -- Since `A \ B ⊆ A`, their closures satisfy the same inclusion.
  have hsubset : closure (A \ B) ⊆ closure A :=
    closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)
  -- Monotonicity of `interior` yields the desired subset relation.
  exact (interior_mono hsubset) hx

theorem not_P3_of_interior_closure_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntClEmpty : interior (closure (A : Set X)) = (∅ : Set X)) (hne : A.Nonempty) :
    ¬ Topology.P3 A := by
  intro hP3
  -- `P3` together with non-emptiness gives a point in `interior (closure A)`.
  have hIntNonempty :=
    Topology.interior_closure_nonempty_of_P3 (A := A) hP3 hne
  rcases hIntNonempty with ⟨x, hxInt⟩
  -- This contradicts the assumption that the interior is empty.
  have : x ∈ (∅ : Set X) := by
    simpa [hIntClEmpty] using hxInt
  exact (Set.not_mem_empty x) this

theorem closure_diff_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  simpa using
    (closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A))

theorem interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem P2_iff_P3_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h₁ : Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) :=
    (Topology.P2_closure_interior_iff_open (A := A))
  have h₂ : Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) :=
    (Topology.P3_closure_interior_iff_open (A := A))
  simpa using h₁.trans h₂.symm

theorem interior_iInter_closure_subset {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (⋂ i, closure (A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  have hxAll : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    have hsubset : (⋂ j, closure (A j) : Set X) ⊆ closure (A i) :=
      Set.iInter_subset (fun j => closure (A j)) i
    exact (interior_mono hsubset) hx
  exact Set.mem_iInter.2 hxAll

theorem interior_closure_eq_closure_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    interior (closure A) = closure A := by
  simpa using hOpen.interior_eq

theorem interior_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior A) := by
  exact subset_closure

theorem P1_of_P3_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure A) := by
  exact Topology.P1_of_open_closure (A := A) hOpenCl

theorem P2_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using (Topology.P2_of_open (A := A ∩ B) hOpen)

theorem closure_inter_eq_self_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  have hClosed : IsClosed (A ∩ B) := hA.inter hB
  simpa using hClosed.closure_eq



theorem P2_iff_exists_open_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure (interior A) := by
  constructor
  · intro hP2
    refine ⟨interior (closure (interior A)), isOpen_interior, ?_, interior_subset⟩
    exact hP2
  · rintro ⟨U, hUopen, hAU, hUcl⟩
    dsimp [Topology.P2]
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    have hUsub : U ⊆ interior (closure (interior A)) :=
      interior_maximal hUcl hUopen
    exact hUsub hxU

theorem closure_interior_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem closure_interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  apply closure_mono
  exact interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)

theorem P1_iff_exists_open_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ A ⊆ closure U := by
  constructor
  · intro hP1
    refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
    simpa using hP1
  · rintro ⟨U, hUopen, hUsubA, hAclU⟩
    dsimp [Topology.P1]
    intro x hxA
    have hx_clU : x ∈ closure U := hAclU hxA
    have hUsubInt : (U : Set X) ⊆ interior A :=
      interior_maximal hUsubA hUopen
    have h_cl_subset : closure U ⊆ closure (interior A) :=
      closure_mono hUsubInt
    exact h_cl_subset hx_clU

theorem interior_interior_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior (closure A)) = interior (closure A) := by
  simpa [interior_interior]

theorem interior_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  -- First, show `interior (A ∩ B) ⊆ interior A ∩ B`.
  have h₁ : interior (A ∩ B) ⊆ interior A ∩ interior B :=
    interior_inter_subset (A := A) (B := B)
  have h₁' : interior (A ∩ B) ⊆ interior A ∩ B := by
    simpa [hB.interior_eq] using h₁
  -- Second, show `interior A ∩ B ⊆ interior (A ∩ B)`.
  have h₂ : interior A ∩ B ⊆ interior (A ∩ B) := by
    intro x hx
    rcases hx with ⟨hxIntA, hxB⟩
    -- `x` lies in the open set `interior A ∩ B`, which is contained in `A ∩ B`.
    have hOpen : IsOpen (interior A ∩ B) := isOpen_interior.inter hB
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1, hy.2⟩
    exact
      (interior_maximal hSub hOpen) ⟨hxIntA, hxB⟩
  exact Set.Subset.antisymm h₁' h₂

theorem interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  exact interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)

theorem interior_closure_empty_iff_empty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    interior (closure A) = (∅ : Set X) ↔ A = ∅ := by
  constructor
  · intro hInt
    -- `P3` gives `A ⊆ interior (closure A)`.
    have hSub : (A : Set X) ⊆ interior (closure A) := hP3
    -- Combining with `hInt`, we obtain `A ⊆ ∅`.
    have hSubEmpty : (A : Set X) ⊆ (∅ : Set X) := by
      simpa [hInt] using hSub
    -- Hence `A = ∅`.
    exact Set.Subset.antisymm hSubEmpty (Set.empty_subset _)
  · intro hA
    -- If `A = ∅`, then its closure is `∅`, and so is the interior.
    simpa [hA, closure_empty, interior_empty]

theorem subset_interior_closure_of_subset_of_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3 : Topology.P3 A) (hBA : B ⊆ A) :
    B ⊆ interior (closure A) := by
  intro x hxB
  exact hP3 (hBA hxB)

theorem interior_inter_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  simpa [Set.inter_comm] using
    (interior_inter_right_open (A := B) (B := A) hA)



theorem P3_iUnion_open {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P3 (⋃ i, A i) := by
  -- Each `A i` is open and hence satisfies `P3`.
  have hP3 : ∀ i, Topology.P3 (A i) := fun i => Topology.P3_of_open (A := A i) (hA i)
  exact Topology.P3_iUnion hP3

theorem closure_interior_eq_self_iff_closed {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = interior A ↔ IsClosed (interior A) := by
  constructor
  · intro hEq
    have hClosed : IsClosed (closure (interior A)) := isClosed_closure
    simpa [hEq] using hClosed
  · intro hClosed
    simpa using hClosed.closure_eq

theorem P123_sUnion {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) :
    Topology.P1 (⋃₀ 𝔄) ∧ Topology.P2 (⋃₀ 𝔄) ∧ Topology.P3 (⋃₀ 𝔄) := by
  -- Extract each component property for every `A ∈ 𝔄`.
  have hP1 : ∀ A, A ∈ 𝔄 → Topology.P1 A := fun A h => (hA A h).1
  have hP2 : ∀ A, A ∈ 𝔄 → Topology.P2 A := fun A h => (hA A h).2.1
  have hP3 : ∀ A, A ∈ 𝔄 → Topology.P3 A := fun A h => (hA A h).2.2
  -- Apply the existing `sUnion` lemmas for each property.
  have hP1s : Topology.P1 (⋃₀ 𝔄) := Topology.P1_sUnion hP1
  have hP2s : Topology.P2 (⋃₀ 𝔄) := Topology.P2_sUnion hP2
  have hP3s : Topology.P3 (⋃₀ 𝔄) := Topology.P3_sUnion hP3
  exact ⟨hP1s, hP2s, hP3s⟩

theorem closure_eq_closure_interior_of_P1_iUnion
    {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i)) :
    closure (⋃ i, A i) = closure (interior (⋃ i, A i)) := by
  -- First, obtain `P1` for the union using the existing lemma.
  have hUnion : Topology.P1 (⋃ i, A i) := Topology.P1_iUnion hA
  -- Apply the characterisation of `P1` to relate the two closures.
  exact Topology.closure_eq_closure_interior_of_P1 (A := ⋃ i, A i) hUnion

theorem P1_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} [Nonempty Y] (hA : A.Nonempty) :
    Topology.P1 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P1 A := by
  -- A witness for the nonemptiness of `Set.univ : Set Y`.
  have hB : (Set.univ : Set Y).Nonempty := Set.nonempty_univ
  -- Use the existing equivalence for products.
  have hEquiv :=
    (Topology.P1_prod_iff (A := A) (B := (Set.univ : Set Y)) hA hB)
  -- `P1` holds for the universal set.
  have hP1_univ : Topology.P1 (Set.univ : Set Y) := Topology.P1_univ
  constructor
  · intro hProd
    -- Extract `P1 A` from the equivalence.
    exact (hEquiv.mp hProd).1
  · intro hP1A
    -- Re-assemble the pair to use the equivalence in the other direction.
    exact hEquiv.mpr ⟨hP1A, hP1_univ⟩

theorem P2_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} [Nonempty Y] (hA : A.Nonempty) :
    Topology.P2 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P2 A := by
  -- `Set.univ : Set Y` is nonempty under the given typeclass assumption.
  have hB : (Set.univ : Set Y).Nonempty := Set.nonempty_univ
  -- Invoke the general product equivalence for `P2`.
  have hEquiv :=
    (Topology.P2_prod_iff (A := A) (B := (Set.univ : Set Y)) hA hB)
  -- Use the fact that `P2` holds for `Set.univ`.
  have hP2_univ : Topology.P2 (Set.univ : Set Y) :=
    Topology.P2_univ (X := Y)
  -- Split the equivalence into the desired two implications.
  constructor
  · intro hProd
    exact (hEquiv.mp hProd).1
  · intro hPA
    exact hEquiv.mpr ⟨hPA, hP2_univ⟩

theorem P3_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} [Nonempty Y] (hA : A.Nonempty) :
    Topology.P3 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P3 A := by
  -- A witness that `Set.univ : Set Y` is nonempty.
  have hB : (Set.univ : Set Y).Nonempty := Set.nonempty_univ
  -- Use the general product equivalence for `P3`.
  have hEquiv :=
    (Topology.P3_prod_iff (A := A) (B := (Set.univ : Set Y)) hA hB)
  -- `P3` holds trivially for the whole space.
  have hP3_univ : Topology.P3 (Set.univ : Set Y) := Topology.P3_univ
  constructor
  · intro hProd
    exact (hEquiv.mp hProd).1
  · intro hPA
    exact hEquiv.mpr ⟨hPA, hP3_univ⟩

theorem interior_closure_iUnion_subset {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    (⋃ i, interior (closure (A i))) ⊆ interior (closure (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `closure (A i)` is contained in the closure of the union.
  have hsubset_cl : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Monotonicity of `interior` upgrades the inclusion.
  have hsubset_int :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono hsubset_cl
  exact hsubset_int hx_i

theorem isOpen_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsOpen (interior (closure (A : Set X))) := by
  simpa using (isOpen_interior : IsOpen (interior (closure (A : Set X))))

theorem P123_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] {A : Set X} (hA : A.Nonempty) :
    (Topology.P1 (A ×ˢ (Set.univ : Set Y)) ∧
      Topology.P2 (A ×ˢ (Set.univ : Set Y)) ∧
      Topology.P3 (A ×ˢ (Set.univ : Set Y))) ↔
      (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  -- A witness that `Set.univ : Set Y` is nonempty.
  have hB : (Set.univ : Set Y).Nonempty := Set.nonempty_univ
  -- General equivalence for products.
  have hEquiv :=
    (Topology.P123_prod_iff (A := A) (B := (Set.univ : Set Y)) hA hB)
  -- The triple of properties holds for the whole space.
  have hTripleUniv :
      Topology.P1 (Set.univ : Set Y) ∧
        Topology.P2 (Set.univ : Set Y) ∧
        Topology.P3 (Set.univ : Set Y) :=
    Topology.P123_univ (X := Y)
  constructor
  · intro hProd
    -- Extract the factor corresponding to `A`.
    exact (hEquiv.mp hProd).1
  · intro hTripleA
    -- Combine the triple for `A` with that for `univ` and reassemble.
    have hPair :
        (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ∧
          (Topology.P1 (Set.univ : Set Y) ∧
            Topology.P2 (Set.univ : Set Y) ∧
            Topology.P3 (Set.univ : Set Y)) :=
      ⟨hTripleA, hTripleUniv⟩
    exact hEquiv.mpr hPair

theorem closure_interior_union_eq_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure (interior A) ∪ closure (interior B) := by
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  have hIntUnion : interior (A ∪ B) = A ∪ B := (hA.union hB).interior_eq
  simpa [hIntA, hIntB, hIntUnion, closure_union]

theorem interior_closure_diff_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  -- Step 1:  `A \ B` is contained in `A ∪ B`.
  have hSub : (A \ B : Set X) ⊆ A ∪ B := by
    intro y hy
    exact Or.inl hy.1
  -- Step 2:  Taking closures preserves the inclusion.
  have hClSub : closure (A \ B) ⊆ closure (A ∪ B) :=
    closure_mono hSub
  -- Step 3:  Monotonicity of `interior` yields the desired result.
  exact (interior_mono hClSub) hx

theorem closure_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure A).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hCl
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · exfalso
      have hAeq : (A : Set X) = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have hCleq : closure A = (∅ : Set X) := by
        simpa [hAeq, closure_empty]
      have hContr : (∅ : Set X).Nonempty := by
        simpa [hCleq] using hCl
      rcases hContr with ⟨x, hx⟩
      exact hx.elim
  · intro hA
    rcases hA with ⟨x, hxA⟩
    exact ⟨x, subset_closure hxA⟩

theorem P123_iUnion_open {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P1 (⋃ i, A i) ∧ Topology.P2 (⋃ i, A i) ∧ Topology.P3 (⋃ i, A i) := by
  exact
    ⟨Topology.P1_iUnion_open hA,
      Topology.P2_iUnion_open hA,
      Topology.P3_iUnion_open hA⟩

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (closure (A ∪ B : Set X)) := by
  have hUnion : Topology.P1 (A ∪ B) :=
    Topology.P1_union (A := A) (B := B) hA hB
  exact Topology.P1_closure_of_P1 (A := A ∪ B) hUnion

theorem interior_closure_iInter_eq {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsClosed (A i)) :
    interior (closure (⋂ i, A i)) = interior (⋂ i, A i) := by
  have hEq : closure (⋂ i, A i) = (⋂ i, A i) :=
    (closure_iInter_eq_iInter (A := A) (hA := hA))
  simpa [hEq]

theorem closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro hCl
    -- `interior A` is contained in its closure, which is empty by assumption.
    have hSub : (interior A : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ closure (interior A) := subset_closure hx
      simpa [hCl] using this
    -- Hence `interior A` itself is empty.
    exact (Set.Subset.antisymm hSub (Set.empty_subset _))
  · intro hInt
    -- If `interior A` is empty, so is its closure.
    simpa [hInt, closure_empty]

theorem closure_interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hne : A.Nonempty) : (closure (interior A)).Nonempty := by
  rcases hne with ⟨x, hxA⟩
  exact ⟨x, hP1 hxA⟩

theorem subset_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A ⊆ closure (interior A)) := by
  intro hP2
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hsubset hxInt

theorem closure_interior_nonempty_iff_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · intro hCl
    by_contra hInt
    have hIntEq : interior A = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hInt
    have hClEq : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEq, closure_empty]
    rcases hCl with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hClEq] using hx
    exact (Set.not_mem_empty x) this
  · intro hInt
    rcases hInt with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩

theorem closure_union_eq_self_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B) = A ∪ B := by
  have hClosed : IsClosed (A ∪ B) := hA.union hB
  simpa using hClosed.closure_eq

theorem exists_open_superset_same_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  intro hP3
  refine ⟨interior (closure A), isOpen_interior, ?_, ?_⟩
  ·
    exact hP3
  ·
    simpa using
      (Topology.closure_eq_closure_interior_closure_of_P3 (A := A) hP3).symm

theorem isOpen_closure_iff_interior_closure_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ interior (closure A) = closure A := by
  constructor
  · intro hOpen
    exact hOpen.interior_eq
  · intro hEq
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    simpa [hEq] using hOpen

theorem interior_closure_inter_closure_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure A ∩ closure B) = interior A ∩ interior B := by
  -- Since `A` and `B` are closed, their closures are the sets themselves.
  have hA_cl : closure A = (A : Set X) := hA.closure_eq
  have hB_cl : closure B = (B : Set X) := hB.closure_eq
  -- Rewrite and apply the existing equality for closed intersections.
  simpa [hA_cl, hB_cl] using
    (interior_inter_eq_of_closed (A := A) (B := B) hA hB)

theorem closure_interior_subset_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  -- The interior of `A` is contained in `A`.
  have hsubset : (interior A : Set X) ⊆ A := interior_subset
  -- Since `A` is closed, its closure is itself. Apply `closure_minimal`.
  exact closure_minimal hsubset hA

theorem exists_open_subset_same_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ closure U = closure A := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  have hEq :
      closure (interior A) = closure A :=
    (Topology.closure_eq_closure_interior_of_P1 (A := A) hP1).symm
  simpa [hEq]



theorem closure_eq_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    closure A = closure (interior (closure A)) := by
  -- First, recall the equality furnished by `P1`.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) h
  -- Establish the two inclusions.
  apply subset_antisymm
  ·
    -- `closure A ⊆ closure (interior (closure A))`
    have hsubset : closure (interior A) ⊆ closure (interior (closure A)) :=
      closure_interior_subset_closure_interior_closure (A := A)
    simpa [hEq] using hsubset
  ·
    -- `closure (interior (closure A)) ⊆ closure A`
    have hsubset : interior (closure A) ⊆ closure A := interior_subset
    have hclosure :
        closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono hsubset
    simpa [closure_closure] using hclosure

theorem closure_eq_closure_interior_closure_of_P1_alt
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    closure A = closure (interior (closure A)) := by
  -- First, recall the closure equality provided by `P1`.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) h
  -- Establish the two subset inclusions.
  apply Set.Subset.antisymm
  ·
    -- `closure A ⊆ closure (interior (closure A))`
    have hSubInt : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    have hSub : closure (interior A) ⊆ closure (interior (closure A)) :=
      closure_mono hSubInt
    simpa [hEq] using hSub
  ·
    -- `closure (interior (closure A)) ⊆ closure A`
    have hSubInt : (interior (closure A) : Set X) ⊆ closure A :=
      interior_subset
    have hSub : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono hSubInt
    simpa [closure_closure] using hSub

theorem closure_eq_iff_subset_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) = closure B ↔ (A ⊆ closure B ∧ B ⊆ closure A) := by
  constructor
  · intro hEq
    have hAB : (A : Set X) ⊆ closure B := by
      intro x hxA
      have : x ∈ closure A := (subset_closure : A ⊆ closure A) hxA
      simpa [hEq] using this
    have hBA : (B : Set X) ⊆ closure A := by
      intro x hxB
      have : x ∈ closure B := (subset_closure : B ⊆ closure B) hxB
      simpa [hEq] using this
    exact And.intro hAB hBA
  · rintro ⟨hAB, hBA⟩
    apply Set.Subset.antisymm
    ·
      have hClosed : IsClosed (closure B) := isClosed_closure
      exact closure_minimal hAB hClosed
    ·
      have hClosed : IsClosed (closure A) := isClosed_closure
      exact closure_minimal hBA hClosed

theorem interior_prod_closure_eq_prod_interiors
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    interior (closure (A : Set X) ×ˢ closure (B : Set Y)) =
      interior (closure A) ×ˢ interior (closure B) := by
  simpa [interior_prod_eq]

theorem closed_eq_univ_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    A = (Set.univ : Set X) := by
  simpa [hClosed.closure_eq] using hDense

theorem closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simp [interior_univ, closure_univ]

theorem P1_sUnion_open {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → IsOpen A) :
    Topology.P1 (⋃₀ 𝔄) := by
  -- First, produce `P1` for every member of `𝔄` using openness.
  have hP1 : ∀ A, A ∈ 𝔄 → Topology.P1 A := by
    intro A hA_mem
    exact Topology.P1_of_open (A := A) (hA A hA_mem)
  -- Apply the existing `sUnion` lemma for `P1`.
  exact Topology.P1_sUnion hP1

theorem closure_eq_closure_interior_closure_of_P1'
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    closure A = closure (interior (closure A)) := by
  -- From `P1`, we already have `closure A = closure (interior A)`.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) h
  -- We establish the desired equality via double inclusion.
  apply subset_antisymm
  ·
    -- First inclusion: `closure A ⊆ closure (interior (closure A))`.
    have h₁ : closure (interior A) ⊆ closure (interior (closure A)) := by
      -- Since `A ⊆ closure A`, we have `interior A ⊆ interior (closure A)`.
      have hSub : (interior A : Set X) ⊆ interior (closure A) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      -- Taking closures preserves inclusions.
      exact closure_mono hSub
    simpa [hEq] using h₁
  ·
    -- Second inclusion: `closure (interior (closure A)) ⊆ closure A`.
    have h₂ : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    -- Again, taking closures preserves inclusions and `closure (closure A) = closure A`.
    simpa [closure_closure] using closure_mono h₂

theorem interior_prod_subset_interior_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (interior A) ×ˢ (interior B) ⊆ interior (A ×ˢ B) := by
  intro p hp
  -- `interior A ×ˢ interior B` is open.
  have hOpen : IsOpen ((interior A) ×ˢ (interior B)) :=
    (isOpen_interior).prod isOpen_interior
  -- It is contained in `A ×ˢ B`.
  have hSub : ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ A ×ˢ B := by
    intro q hq
    exact ⟨(interior_subset hq.1), (interior_subset hq.2)⟩
  -- Apply `interior_maximal`.
  exact interior_maximal hSub hOpen hp

theorem P2_prod_right_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB_open : IsOpen B) (hB_nonempty : B.Nonempty) :
    Topology.P2 (A ×ˢ B) ↔ Topology.P2 A := by
  constructor
  · intro hProd
    exact
      Topology.P2_of_P2_prod_left (A := A) (B := B) hB_nonempty hProd
  · intro hA
    exact Topology.P2_prod_right_open (A := A) (B := B) hA hB_open

theorem P1_prod_right_open_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB_open : IsOpen B) (hB_nonempty : B.Nonempty) :
    Topology.P1 (A ×ˢ B) ↔ Topology.P1 A := by
  constructor
  · intro hProd
    exact
      Topology.P1_of_P1_prod_left (A := A) (B := B) hB_nonempty hProd
  · intro hPA
    exact
      Topology.P1_prod_right_open (A := A) (B := B) hPA hB_open

theorem P3_prod_right_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB_open : IsOpen B) (hB_nonempty : B.Nonempty) :
    Topology.P3 (A ×ˢ B) ↔ Topology.P3 A := by
  constructor
  · intro hProd
    exact Topology.P3_of_P3_prod_left (A := A) (B := B) hB_nonempty hProd
  · intro hA
    exact Topology.P3_prod_right_open (A := A) (B := B) hA hB_open

theorem closure_union_closure_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ closure B) = closure (A ∪ B) := by
  apply subset_antisymm
  ·
    -- First inclusion: `closure (A ∪ closure B) ⊆ closure (A ∪ B)`.
    have hSub : (A ∪ closure B : Set X) ⊆ closure (A ∪ B) := by
      intro x hx
      cases hx with
      | inl hA =>
          -- `x ∈ A`, hence `x ∈ closure (A ∪ B)` by closure monotonicity.
          exact subset_closure (Or.inl hA)
      | inr hClB =>
          -- `x ∈ closure B`, and `closure B ⊆ closure (A ∪ B)`.
          have : closure B ⊆ closure (A ∪ B) :=
            closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
          exact this hClB
    have : closure (A ∪ closure B) ⊆ closure (closure (A ∪ B)) :=
      closure_mono hSub
    simpa [closure_closure] using this
  ·
    -- Second inclusion: `closure (A ∪ B) ⊆ closure (A ∪ closure B)`.
    have hSub : (A ∪ B : Set X) ⊆ A ∪ closure B := by
      intro x hx
      cases hx with
      | inl hA => exact Or.inl hA
      | inr hB => exact Or.inr (subset_closure hB)
    exact (closure_mono hSub)

theorem interior_closure_subset_closure' {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure A := by
  exact interior_subset

theorem closure_inter_interior_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure (A ∩ B) := by
  -- First, observe the straightforward set inclusion.
  have hSub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨hx.1, (interior_subset : interior B ⊆ B) hx.2⟩
  -- Taking closures preserves inclusions.
  exact closure_mono hSub

theorem closure_union_closure_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ B : Set X) = closure (A ∪ B) := by
  apply subset_antisymm
  ·
    -- Show `closure (closure A ∪ B)` is contained in `closure (A ∪ B)`.
    have hSub : (closure A ∪ B : Set X) ⊆ closure (A ∪ B) := by
      intro x hx
      cases hx with
      | inl hClA =>
          have : closure A ⊆ closure (A ∪ B) :=
            closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
          exact this hClA
      | inr hB =>
          exact subset_closure (Or.inr hB)
    have : closure (closure A ∪ B) ⊆ closure (closure (A ∪ B)) :=
      closure_mono hSub
    simpa [closure_closure] using this
  ·
    -- Show `closure (A ∪ B)` is contained in `closure (closure A ∪ B)`.
    have hSub : (A ∪ B : Set X) ⊆ closure A ∪ B := by
      intro x hx
      cases hx with
      | inl hA   => exact Or.inl (subset_closure hA)
      | inr hB   => exact Or.inr hB
    exact closure_mono hSub

theorem P123_prod_right_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB_open : IsOpen B) (hB_nonempty : B.Nonempty) :
    (Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B)) ↔
      (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  -- Individual equivalences for each property with an open, nonempty right factor.
  have hP1Equiv :=
    Topology.P1_prod_right_open_iff (A := A) (B := B) hB_open hB_nonempty
  have hP2Equiv :=
    Topology.P2_prod_right_open_iff (A := A) (B := B) hB_open hB_nonempty
  have hP3Equiv :=
    Topology.P3_prod_right_open_iff (A := A) (B := B) hB_open hB_nonempty
  constructor
  · rintro ⟨hP1Prod, hP2Prod, hP3Prod⟩
    exact
      ⟨hP1Equiv.mp hP1Prod, hP2Equiv.mp hP2Prod, hP3Equiv.mp hP3Prod⟩
  · rintro ⟨hP1A, hP2A, hP3A⟩
    exact
      ⟨hP1Equiv.mpr hP1A, hP2Equiv.mpr hP2A, hP3Equiv.mpr hP3A⟩

theorem P2_prod_left_open_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hA_nonempty : A.Nonempty) :
    Topology.P2 (A ×ˢ B) ↔ Topology.P2 B := by
  constructor
  · intro hProd
    exact
      Topology.P2_of_P2_prod_right (A := A) (B := B) hA_nonempty hProd
  · intro hPB
    exact
      Topology.P2_prod_left_open (A := A) (B := B) hA_open hPB

theorem P2_of_P3_and_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A)
    (hEq : interior (closure A) = interior (closure (interior A))) :
    Topology.P2 A := by
  have h : Topology.P3 A ∧
      interior (closure A) = interior (closure (interior A)) := ⟨hP3, hEq⟩
  exact (Topology.P2_iff_P3_and_interior_closure_eq (A := A)).mpr h

theorem P3_prod_left_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hA_nonempty : A.Nonempty) :
    Topology.P3 (A ×ˢ B) ↔ Topology.P3 B := by
  constructor
  · intro hProd
    exact Topology.P3_of_P3_prod_right (A := A) (B := B) hA_nonempty hProd
  · intro hPB
    exact Topology.P3_prod_left_open (A := A) (B := B) hA_open hPB

theorem P1_prod_left_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hA_nonempty : A.Nonempty) :
    Topology.P1 (A ×ˢ B) ↔ Topology.P1 B := by
  constructor
  · intro hProd
    -- Extract `P1` for `B` from the product using the projection lemma.
    exact
      Topology.P1_of_P1_prod_right (A := A) (B := B) hA_nonempty hProd
  · intro hPB
    -- Build `P1` for the product from `P1 B` and the openness of `A`.
    exact
      Topology.P1_prod_left_open (A := A) (B := B) hA_open hPB

theorem P123_prod_left_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hA_nonempty : A.Nonempty) :
    (Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B)) ↔
      (Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B) := by
  -- Equivalences for each property with an open, nonempty left factor.
  have hP1Equiv :=
    Topology.P1_prod_left_open_iff (A := A) (B := B) hA_open hA_nonempty
  have hP2Equiv :=
    Topology.P2_prod_left_open_iff (A := A) (B := B) hA_open hA_nonempty
  have hP3Equiv :=
    Topology.P3_prod_left_open_iff (A := A) (B := B) hA_open hA_nonempty
  constructor
  · rintro ⟨hP1Prod, hP2Prod, hP3Prod⟩
    exact
      ⟨hP1Equiv.mp hP1Prod, hP2Equiv.mp hP2Prod, hP3Equiv.mp hP3Prod⟩
  · rintro ⟨hP1B, hP2B, hP3B⟩
    exact
      ⟨hP1Equiv.mpr hP1B, hP2Equiv.mpr hP2B, hP3Equiv.mpr hP3B⟩

theorem P1_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P1 (closure (A : Set X)) := by
  simpa [hDense] using (Topology.P1_univ (X := X))

theorem P1_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} (hB : B.Nonempty) :
    Topology.P1 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P1 B := by
  -- A witness that `Set.univ : Set X` is nonempty.
  have hA : (Set.univ : Set X).Nonempty := Set.nonempty_univ
  -- Apply the existing product equivalence for `P1`.
  have hEquiv :=
    (Topology.P1_prod_iff (A := (Set.univ : Set X)) (B := B) hA hB)
  -- `P1` holds for the universal set.
  have hP1_univ : Topology.P1 (Set.univ : Set X) := Topology.P1_univ (X := X)
  -- Split the equivalence into the desired two implications.
  constructor
  · intro hProd
    exact (hEquiv.mp hProd).2
  · intro hPB
    exact hEquiv.mpr ⟨hP1_univ, hPB⟩

theorem P3_of_interior_closure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have : x ∈ interior (closure A) := by
    simpa [h] using hxA
  exact this

theorem interior_sUnion_open {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → IsOpen (A : Set X)) :
    interior (⋃₀ 𝔄 : Set X) = ⋃₀ 𝔄 := by
  have hOpen : IsOpen (⋃₀ 𝔄 : Set X) := by
    refine isOpen_sUnion ?_
    intro U hU
    exact hA U hU
  simpa [hOpen.interior_eq]

theorem P2_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (closure A)) ↔ Topology.P2 (closure A) := by
  simpa [closure_closure]

theorem P123_univ_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} (hB : B.Nonempty) :
    (Topology.P1 ((Set.univ : Set X) ×ˢ B) ∧
      Topology.P2 ((Set.univ : Set X) ×ˢ B) ∧
      Topology.P3 ((Set.univ : Set X) ×ˢ B)) ↔
      (Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B) := by
  -- `Set.univ : Set X` is nonempty by assumption.
  have hA : (Set.univ : Set X).Nonempty := Set.nonempty_univ
  -- Use the general product equivalence for the triple of properties.
  have hEquiv :=
    (Topology.P123_prod_iff
        (A := (Set.univ : Set X)) (B := B) hA hB)
  -- The triple of properties holds for the universal set.
  have hTripleUniv :
      Topology.P1 (Set.univ : Set X) ∧
        Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) :=
    Topology.P123_univ (X := X)
  constructor
  · intro hProd
    -- Extract the triple for `B` from the equivalence.
    exact (hEquiv.mp hProd).2
  · intro hTripleB
    -- Combine the triple for `B` with the one for `univ`
    -- and reassemble via the equivalence.
    exact
      hEquiv.mpr ⟨hTripleUniv, hTripleB⟩

theorem closure_union_closure_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ closure B : Set X) = closure (A ∪ B) := by
  have h₁ :
      closure (closure A ∪ closure B : Set X) = closure (A ∪ closure B) := by
    simpa using
      (closure_union_closure_left (A := A) (B := closure B))
  have h₂ : closure (A ∪ closure B : Set X) = closure (A ∪ B) :=
    closure_union_closure_right (A := A) (B := B)
  simpa using (h₁.trans h₂)

theorem subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A ⊆ closure (interior A)) := by
  intro hP1
  exact hP1

theorem P1_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) = B) : Topology.P1 A ↔ Topology.P1 B := by
  simpa [h]

theorem P1_iff_subset_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 A ↔ A ⊆ closure (interior A) := by
  rfl

theorem closure_interior_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (interior A ∩ B) := by
  have hInt : interior (A ∩ B) = interior A ∩ B :=
    interior_inter_right_open (A := A) (B := B) hB
  simpa [hInt]

theorem P2_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} (hB : B.Nonempty) :
    Topology.P2 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P2 B := by
  -- A witness that `Set.univ : Set X` is nonempty.
  have hA : (Set.univ : Set X).Nonempty := Set.nonempty_univ
  -- General equivalence for products.
  have hEquiv :=
    (Topology.P2_prod_iff
        (A := (Set.univ : Set X)) (B := B) hA hB)
  -- `P2` holds for the whole space.
  have hP2_univ : Topology.P2 (Set.univ : Set X) :=
    Topology.P2_univ (X := X)
  constructor
  · intro hProd
    -- Extract the second component from the equivalence.
    exact (hEquiv.mp hProd).2
  · intro hPB
    -- Combine with the universal set's `P2` to apply the equivalence.
    exact hEquiv.mpr ⟨hP2_univ, hPB⟩



theorem closure_union_interior_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  exact
    closure_mono
      (interior_union_subset (A := A) (B := B))

theorem closure_union_interior_subset_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∪ interior B) ⊆ closure (A ∪ B) := by
  -- The subset relation on the underlying sets
  have hSub : (A ∪ interior B : Set X) ⊆ A ∪ B := by
    intro x hx
    cases hx with
    | inl hA   => exact Or.inl hA
    | inr hInt => exact Or.inr ((interior_subset : interior B ⊆ B) hInt)
  -- Taking closures preserves inclusions
  exact closure_mono hSub

theorem iUnion_closure_subset_closure_iUnion {X ι : Type*} [TopologicalSpace X]
    {A : ι → Set X} :
    (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hsubset : closure (A i) ⊆ closure (⋃ j, A j) :=
    closure_mono (Set.subset_iUnion _ _)
  exact hsubset hx_i

theorem P2_closure_interior_closure_iff_open {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  have hClosed : IsClosed (closure (interior (closure A))) := isClosed_closure
  simpa using
    (Topology.P2_iff_open_of_closed
        (A := closure (interior (closure A))) hClosed)

theorem not_P2_of_interior_closure_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntClEmpty : interior (closure (A : Set X)) = (∅ : Set X))
    (hne : A.Nonempty) :
    ¬ Topology.P2 A := by
  intro hP2
  -- From `P2` we obtain `P3`.
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  -- Pick an element of the non-empty set `A`.
  rcases hne with ⟨x, hxA⟩
  -- `P3` sends it into `interior (closure A)`.
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- But this interior is empty, contradicting membership.
  have : x ∈ (∅ : Set X) := by
    simpa [hIntClEmpty] using hxInt
  exact (Set.not_mem_empty _).elim this

theorem closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- The interior of `closure A` is contained in `closure A`.
  have h₁ : (interior (closure A) : Set X) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h₂

theorem closure_interior_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    (closure (interior A)).Nonempty ↔ A.Nonempty := by
  have h₁ :
      (closure (interior A)).Nonempty ↔ (interior A).Nonempty :=
    (closure_interior_nonempty_iff_interior_nonempty (A := A))
  have h₂ : (interior A).Nonempty ↔ A.Nonempty :=
    (interior_nonempty_iff_nonempty_of_P2 (A := A) hP2)
  simpa using h₁.trans h₂

theorem P3_of_P1_and_open_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A)
    (hOpen : IsOpen (closure (interior A))) :
    Topology.P3 A := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- Step 1: `P1` sends `x` into `closure (interior A)`.
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  -- Step 2: since `closure (interior A)` is open, its interior is itself.
  have hIntEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Reinterpret membership using the interior.
  have hxInt : x ∈ interior (closure (interior A)) := by
    simpa [hIntEq] using hxCl
  -- Step 3: monotonicity of `interior` gives the desired containment.
  have hsubset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_closure_interior_subset (A := A)
  exact hsubset hxInt

theorem P123_union_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  rcases hA with ⟨hP1A, hP2A, hP3A⟩
  have hP1Union : Topology.P1 (A ∪ B) :=
    Topology.P1_union_right_open (A := A) (B := B) hP1A hB_open
  have hP2Union : Topology.P2 (A ∪ B) :=
    Topology.P2_union_right_open (A := A) (B := B) hP2A hB_open
  have hP3Union : Topology.P3 (A ∪ B) :=
    Topology.P3_union_right_open (A := A) (B := B) hP3A hB_open
  exact ⟨hP1Union, hP2Union, hP3Union⟩

theorem P123_union_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P123_union_right_open (A := B) (B := A) hB hA_open)

theorem P3_of_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior (closure A)))) := by
  simpa using
    (Topology.P3_of_open
        (A := interior (closure (interior (closure A)))) isOpen_interior)

theorem P3_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P3 (closure (A : Set X)) := by
  simpa [hDense] using (Topology.P3_univ (X := X))

theorem interior_union_of_interiors {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((interior A) ∪ (interior B)) = (interior A) ∪ (interior B) := by
  -- The union of two open sets is open.
  have hOpen : IsOpen ((interior A) ∪ (interior B)) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  -- For open sets, the interior equals the set itself.
  simpa [hOpen.interior_eq]

theorem P3_of_P1_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 A ∧ Topology.P2 A) → Topology.P3 A := by
  rintro ⟨_, hP2⟩
  exact Topology.P2_implies_P3 (A := A) hP2



theorem P2_iff_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 A ↔ A ⊆ interior (closure (interior A)) := by
  rfl

theorem P3_iff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 A ↔ A ⊆ interior (closure A) := by
  rfl

theorem closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure A)))))) =
      closure (interior (closure A)) := by
  -- Apply `closure` to both sides of the interior-level equality and simplify.
  have h :=
    congrArg (fun s : Set X => closure s)
      (interior_closure_interior_closure_interior_closure_eq (A := A))
  simpa using h

theorem interior_closure_empty_iff_empty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP2 : Topology.P2 A) :
    interior (closure A) = (∅ : Set X) ↔ A = ∅ := by
  -- Upgrade `P2` to `P3` in order to use the existing equivalence.
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  -- Apply the equivalence already proved for `P3`.
  simpa using (interior_closure_empty_iff_empty_of_P3 (A := A) hP3)

theorem closure_interior_prod_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    closure (interior (A ×ˢ B)) = closure ((interior A) ×ˢ (interior B)) := by
  simpa [interior_prod_eq]

theorem P3_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} (hB : B.Nonempty) :
    Topology.P3 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P3 B := by
  -- `Set.univ : Set X` is nonempty by assumption.
  have hA : (Set.univ : Set X).Nonempty := Set.nonempty_univ
  -- Apply the general product equivalence for `P3`.
  have hEquiv :=
    (Topology.P3_prod_iff
        (A := (Set.univ : Set X)) (B := B) hA hB)
  -- `P3` holds trivially for the universal set.
  have hP3_univ : Topology.P3 (Set.univ : Set X) := Topology.P3_univ
  constructor
  · intro hProd
    -- Extract the factor corresponding to `B`.
    exact (hEquiv.mp hProd).2
  · intro hPB
    -- Combine with the universal factor and reassemble via the equivalence.
    exact hEquiv.mpr ⟨hP3_univ, hPB⟩

theorem closure_inter_closure_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- Membership in `closure A` comes from the left inclusion.
  have hA : x ∈ closure A := by
    have hsubset : (A ∩ closure B : Set X) ⊆ A := Set.inter_subset_left
    exact (closure_mono hsubset) hx
  -- Membership in `closure B` comes from the right inclusion.
  have hB : x ∈ closure B := by
    have hsubset : (A ∩ closure B : Set X) ⊆ closure B := Set.inter_subset_right
    have hcl : closure (A ∩ closure B) ⊆ closure (closure B) :=
      closure_mono hsubset
    have : x ∈ closure (closure B) := hcl hx
    simpa [closure_closure] using this
  exact ⟨hA, hB⟩

theorem closure_closure_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]

theorem interior_iInter_subset_iInter_interior
    {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (⋂ i, A i) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- For each index `i`, show `x ∈ interior (A i)`.
  have hx_all : ∀ i, x ∈ interior (A i) := by
    intro i
    -- The intersection is contained in each `A i`.
    have hsubset : (⋂ j, A j) ⊆ A i :=
      Set.iInter_subset (fun j => A j) i
    -- Monotonicity of `interior` transfers membership.
    exact (interior_mono hsubset) hx
  -- Aggregate the memberships into the intersection of interiors.
  exact Set.mem_iInter.2 hx_all

theorem P123_of_P1_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- Obtain `P2` and `P3` from the given assumptions.
  have hP2 : Topology.P2 A := Topology.P2_of_P1_and_open_closure (A := A) hP1 hOpenCl
  have hP3 : Topology.P3 A := Topology.P3_of_P1_and_open_closure (A := A) hP1 hOpenCl
  exact ⟨hP1, hP2, hP3⟩

theorem exists_open_superset_same_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact exists_open_superset_same_closure_of_P3 (A := A) hP3

theorem P2_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) = B) :
    Topology.P2 A ↔ Topology.P2 B := by
  simpa [Topology.P2, h]

theorem P3_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- Every open set satisfies `P3`.
  simpa using Topology.P3_of_open (A := A ∩ B) hOpen

theorem closure_interior_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simp [interior_empty, closure_empty]

theorem closure_union_interior_eq_closure_union_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior A ∪ interior B : Set X) = closure (interior (A ∪ B)) := by
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  have hIntUnion : interior (A ∪ B) = A ∪ B := (hA.union hB).interior_eq
  simpa [hIntA, hIntB, hIntUnion]

theorem isClosed_of_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = A) : IsClosed A := by
  simpa [h] using (isClosed_closure : IsClosed (closure (interior A)))

theorem P2_sUnion_open {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → IsOpen (A : Set X)) :
    Topology.P2 (⋃₀ 𝔄) := by
  -- Every open set satisfies `P2`.
  have hP2 : ∀ A, A ∈ 𝔄 → Topology.P2 A := by
    intro A hA_mem
    exact Topology.P2_of_open (A := A) (hA A hA_mem)
  -- Apply the existing `sUnion` lemma for `P2`.
  exact Topology.P2_sUnion hP2

theorem closure_interior_closure_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure A))) =
      closure (interior (closure A)) := by
  have hInt : interior (closure (closure A)) = interior (closure A) := by
    simpa [closure_closure] using interior_closure_closure_eq (A := A)
  simpa [hInt]

theorem interior_nonempty_iff_nonempty_of_closed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) :
    (interior A).Nonempty ↔ A.Nonempty := by
  have hEq : interior A = A :=
    interior_eq_self_of_closed_of_P3 (A := A) hClosed hP3
  simpa [hEq]

theorem interior_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hIntA =>
      -- Step 1: `interior A ⊆ interior (A ∪ B)`.
      have h₁ : interior A ⊆ interior (A ∪ B) := by
        apply interior_mono
        exact Set.subset_union_left
      -- Step 2: `interior (A ∪ B) ⊆ interior (closure (A ∪ B))`.
      have h₂ : interior (A ∪ B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact subset_closure
      exact h₂ (h₁ hIntA)
  | inr hIntB =>
      -- The argument is symmetric for `interior B`.
      have h₁ : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        exact Set.subset_union_right
      have h₂ : interior (A ∪ B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact subset_closure
      exact h₂ (h₁ hIntB)

theorem P1_iff_P2_and_P3_of_open_fixed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Equivalences already established for open sets.
  have h12 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_open (A := A) hA
  have h13 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_open (A := A) hA
  constructor
  · intro hP1
    exact ⟨h12.mp hP1, h13.mp hP1⟩
  · rintro ⟨hP2, _hP3⟩
    exact h12.mpr hP2

theorem P123_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  rcases hA with ⟨hP1A, hP2A, hP3A⟩
  have hP1 : Topology.P1 (A ∩ B) :=
    Topology.P1_inter_right_open (A := A) (B := B) hP1A hB_open
  have hP2 : Topology.P2 (A ∩ B) :=
    Topology.P2_inter_right_open (A := A) (B := B) hP2A hB_open
  have hP3 : Topology.P3 (A ∩ B) :=
    Topology.P3_inter_right_open (A := A) (B := B) hP3A hB_open
  exact ⟨hP1, hP2, hP3⟩

theorem P2_union_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A ∪ (∅ : Set X)) ↔ Topology.P2 A := by
  simpa [Set.union_empty]

theorem closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A)))))))
        = closure (interior (closure (interior (closure (interior A))))) := by
          simpa using
            (closure_interior_closure_interior_closure_eq
                (A := closure (interior (closure (interior A)))))
    _ = closure (interior (closure (interior A))) := by
          simpa using
            (closure_interior_closure_interior_closure_eq
                (A := closure (interior A)))
    _ = closure (interior A) := by
          simpa using
            (closure_interior_closure_interior_closure_eq (A := A))

theorem P2_inter_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A ∩ (Set.univ : Set X)) ↔ Topology.P2 A := by
  simpa [Set.inter_univ]

theorem closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hIncl : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hIncl hA
  | inr hB =>
      have hIncl : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hIncl hB

theorem interior_prod_nonempty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (interior A).Nonempty → (interior B).Nonempty → (interior (A ×ˢ B)).Nonempty := by
  intro hA hB
  rcases hA with ⟨x, hx⟩
  rcases hB with ⟨y, hy⟩
  have : ((x, y) : X × Y) ∈ interior (A ×ˢ B) := by
    -- Rewrite the target interior using `interior_prod_eq`.
    have hMem : ((x, y) : X × Y) ∈ interior A ×ˢ interior B := ⟨hx, hy⟩
    simpa [interior_prod_eq] using hMem
  exact ⟨(x, y), this⟩