

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hIntSubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hClosSubset : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono hClosSubset
  exact Set.Subset.trans hP2 hIntSubset

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have hIntSubset : interior (closure (interior A)) ⊆ closure (interior A) := by
    exact interior_subset
  exact Set.Subset.trans hP2 hIntSubset

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have : closure A ⊆ closure (closure (interior A)) := by
      exact closure_mono h
    simpa [closure_closure] using this
  ·
    exact closure_mono interior_subset

theorem P1_of_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = closure (interior A)) :
    Topology.P1 A := by
  have hSubset : A ⊆ closure (interior A) := by
    simpa [h] using (subset_closure : A ⊆ closure A)
  exact hSubset

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro h
    exact closure_eq_closure_interior_of_P1 h
  · intro h
    exact P1_of_closure_eq_closure_interior h

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    closure A = closure (interior A) := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.closure_eq_closure_interior_of_P1 hP1

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  -- `interior A` coincides with `A` since `A` is open
  have hInt : interior A = A := hA.interior_eq
  -- an open set is contained in the interior of its closure
  have hGoal : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  -- rewrite the target using `hInt`
  have hClosEq : closure (interior A) = closure A := by
    simpa [hInt]
  have : A ⊆ interior (closure (interior A)) := by
    simpa [hClosEq] using hGoal
  exact this

theorem P3_closed_iff_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  -- first, rewrite `closure A` using closedness of `A`
  have hClosure : closure A = A := hA_closed.closure_eq
  unfold Topology.P3
  constructor
  · intro hP3
    -- from `P3`, deduce `A ⊆ interior A`
    have hSub : A ⊆ interior A := by
      simpa [hClosure] using hP3
    -- combine with `interior_subset` to get equality
    have hEq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hSub
    -- use the fact that `interior A` is open
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using hOpenInt
  · intro hOpen
    -- an open set is contained in the interior of its closure
    exact interior_maximal subset_closure hOpen

theorem interior_closure_eq_interior_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure A) = interior (closure (interior A)) := by
  have hClosEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 hP1
  simpa [hClosEq] using
    (rfl : interior (closure A) = interior (closure A))

theorem interior_closure_eq_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    interior (closure A) = interior (closure (interior A)) := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.interior_closure_eq_interior_closure_interior_of_P1 hP1

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  -- An open set is contained in the interior of its closure.
  exact
    (interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA)

theorem P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.P2_of_open hOpen

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) :
    Topology.P3 A := by
  have hInt : interior (closure A) = closure A := hOpen.interior_eq
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  simpa [Topology.P3, hInt] using hSub

theorem P2_closed_iff_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  -- `P3` and openness are equivalent for closed sets
  have hP3_iff_open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_open hA_closed
  constructor
  · intro hP2
    -- `P2` ⇒ `P3` ⇒ `IsOpen`
    have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
    exact (hP3_iff_open).1 hP3
  · intro hOpen
    -- `IsOpen` ⇒ `P2`
    exact Topology.P2_of_open hOpen

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  -- Since `A` is open, its interior coincides with itself.
  have hInt : interior A = A := hA.interior_eq
  -- Every set is contained in the closure of itself.
  have : (A : Set X) ⊆ closure (interior A) := by
    simpa [hInt] using (subset_closure : A ⊆ closure A)
  exact this

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hPA hPB
  -- `A` is contained in the desired set
  have hA : (A : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hA₁ : (A : Set X) ⊆ closure (interior A) := hPA
    have hA₂ : interior A ⊆ interior (A ∪ B) := by
      apply interior_mono
      intro x hx
      exact Or.inl hx
    exact Set.Subset.trans hA₁ (closure_mono hA₂)
  -- `B` is contained in the desired set
  have hB : (B : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hB₁ : (B : Set X) ⊆ closure (interior B) := hPB
    have hB₂ : interior B ⊆ interior (A ∪ B) := by
      apply interior_mono
      intro x hx
      exact Or.inr hx
    exact Set.Subset.trans hB₁ (closure_mono hB₂)
  -- combine the two inclusions
  intro x hx
  cases hx with
  | inl hxA => exact hA hxA
  | inr hxB => exact hB hxB

theorem P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  have hP2 : Topology.P2 (interior A) := Topology.P2_interior A
  exact Topology.P2_implies_P3 hP2

theorem P1_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) (h : ∀ i, Topology.P1 (A i)) :
    Topology.P1 (⋃ i, A i) := by
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hPi : (A i : Set X) ⊆ closure (interior (A i)) := h i
  have hx_cl : x ∈ closure (interior (A i)) := hPi hxAi
  have h_mono : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    apply closure_mono
    have : interior (A i) ⊆ interior (⋃ j, A j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact h_mono hx_cl

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP3B
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3] at hP3A hP3B ⊢
  -- Goal: `A ∪ B ⊆ interior (closure (A ∪ B))`.
  intro x hx
  cases hx with
  | inl hxA =>
      -- From `P3` for `A`, we know `x ∈ interior (closure A)`.
      have hxA' : x ∈ interior (closure A) := hP3A hxA
      -- This interior is contained in the required interior.
      have hIncl : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        -- First, show `closure A ⊆ closure (A ∪ B)`.
        have hSub : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact closure_mono hSub
      exact hIncl hxA'
  | inr hxB =>
      -- From `P3` for `B`, we know `x ∈ interior (closure B)`.
      have hxB' : x ∈ interior (closure B) := hP3B hxB
      -- This interior is contained in the required interior.
      have hIncl : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        -- First, show `closure B ⊆ closure (A ∪ B)`.
        have hSub : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact closure_mono hSub
      exact hIncl hxB'

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hP2A hP2B
  dsimp [Topology.P2] at hP2A hP2B ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure (interior A)) := hP2A hxA
      have hIncl : interior (closure (interior A))
          ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have : interior A ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact this
        exact this
      exact hIncl hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure (interior B)) := hP2B hxB
      have hIncl : interior (closure (interior B))
          ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have : interior B ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact this
        exact this
      exact hIncl hxB'

theorem P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  intro x hx
  have : (x ∈ closure (interior A)) := subset_closure hx
  simpa [interior_interior] using this

theorem P3_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) (h : ∀ i, Topology.P3 (A i)) :
    Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hx_in : x ∈ interior (closure (A i)) := h i hxAi
  have hIncl : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    apply interior_mono
    have hSub : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono hSub
  exact hIncl hx_in

theorem P2_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) (h : ∀ i, Topology.P2 (A i)) :
    Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hx_in : x ∈ interior (closure (interior (A i))) := h i hxAi
  have hIncl :
      interior (closure (interior (A i)))
        ⊆ interior (closure (interior (⋃ j, A j))) := by
    apply interior_mono
    have hSub :
        closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
      apply closure_mono
      have :
          interior (A i) ⊆ interior (⋃ j, A j) := by
        apply interior_mono
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact this
    exact hSub
  exact hIncl hx_in

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  have hP2_open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_open hA_closed
  have hOpen_P3 : IsOpen A ↔ Topology.P3 A :=
    (Topology.P3_closed_iff_open hA_closed).symm
  exact hP2_open.trans hOpen_P3

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.P2_of_open hOpen

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  exact False.elim hx

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  have hP2 : Topology.P2 (interior (closure A)) :=
    Topology.P2_interior_closure A
  exact Topology.P2_implies_P3 hP2

theorem P1_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.P1_of_open hOpen

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  simp

theorem P2_iff_P3_of_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hEq : closure A = closure (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 hP2
  · intro hP3
    dsimp [Topology.P2] at *
    dsimp [Topology.P3] at hP3
    intro x hx
    have hx' : x ∈ interior (closure A) := hP3 hx
    have hIntEq : interior (closure A) = interior (closure (interior A)) := by
      simpa [hEq]
    simpa [hIntEq] using hx'

theorem interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- First, note that `closure (interior A)` is contained in `closure A`
  have h : closure (interior A) ⊆ closure A := by
    exact closure_mono interior_subset
  -- Taking interiors preserves this inclusion
  exact interior_mono h

theorem P2_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP2A : Topology.P2 A) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  -- Use the equivalence `P2 A ↔ IsOpen A` for closed sets.
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_open hA_closed).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_open hB_closed).1 hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- Apply `P2` for open sets.
  exact Topology.P2_of_open hOpenInter

theorem P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  simp

theorem P1_closed_iff_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  dsimp [Topology.P1]
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    ·
      have hSub : closure (interior A) ⊆ closure A :=
        closure_mono interior_subset
      simpa [hA_closed.closure_eq] using hSub
    ·
      exact hP1
  · intro hEq
    simpa [hEq] using (subset_rfl : A ⊆ A)

theorem P3_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP3A : Topology.P3 A) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Translate `P3` for the closed sets `A` and `B` into their openness.
  have hOpenA : IsOpen A :=
    (Topology.P3_closed_iff_open hA_closed).1 hP3A
  have hOpenB : IsOpen B :=
    (Topology.P3_closed_iff_open hB_closed).1 hP3B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- Apply `P3` for open sets.
  exact Topology.P3_of_open hOpenInter

theorem P2_closure_iff_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P2_closed_iff_open hClosed)

theorem P123_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact ⟨Topology.P1_of_open hA, Topology.P2_of_open hA, Topology.P3_of_open hA⟩

theorem P123_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧ Topology.P2 (interior A) ∧ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using Topology.P123_of_open hOpen

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  -- Goal: `closure A ⊆ closure (interior (closure A))`.
  -- First, rewrite `closure A` using `hP1`.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 hP1
  -- Establish the required inclusion of closures.
  have hIncl : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    have : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono this
  -- Conclude the proof.
  intro x hx
  have hx' : x ∈ closure (interior A) := by
    simpa [hEq] using hx
  exact hIncl hx'

theorem P123_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  simpa using Topology.P123_of_open hOpen

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  exact Topology.P2_of_open hOpen

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact Topology.P2_of_open hA
  · intro hP2
    exact Topology.P2_implies_P1 hP2

theorem P3_closure_iff_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P3_closed_iff_open hClosed)

theorem P2_closure_iff_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P3 (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P2_iff_P3_of_closed hClosed)

theorem interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  exact ⟨x, hxInt⟩

theorem closure_interior_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hx⟩
  have hx' : x ∈ closure (interior A) := hP1 hx
  exact ⟨x, hx'⟩

theorem P123_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  simpa using Topology.P123_of_open hOpenInter

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro _hP1
    exact Topology.P3_of_open hA
  · intro _hP3
    exact Topology.P1_of_open hA

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_open hA
  have hP1P3 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_open hA
  exact hP1P2.symm.trans hP1P3

theorem P3_implies_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  -- From `P3` and closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_closed_iff_open hA_closed).1 hP3
  -- For an open set, the interior coincides with the set itself.
  have hInt : interior A = A := hOpen.interior_eq
  -- Unfold the definition of `P1` and prove the required inclusion.
  dsimp [Topology.P1]
  intro x hxA
  -- View `x` as an element of `interior A` using `hInt`.
  have hxInt : x ∈ interior A := by
    simpa [hInt] using hxA
  -- Any point of `interior A` lies in `closure (interior A)`.
  exact subset_closure hxInt

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  -- `interior A` is contained in `interior (closure A)` since `A ⊆ closure A`.
  have h : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  -- Taking closures preserves inclusions.
  exact closure_mono h

theorem interior_closure_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
  exact Topology.interior_closure_nonempty_of_P3 hP3 hA

theorem P1_iff_P3_of_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure A) = closure (interior A)) :
    Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro hP1
    dsimp [Topology.P1] at hP1
    dsimp [Topology.P3]
    intro x hx
    have hx' : x ∈ closure (interior A) := hP1 hx
    simpa [hEq] using hx'
  · intro hP3
    dsimp [Topology.P3] at hP3
    dsimp [Topology.P1]
    intro x hx
    have hx' : x ∈ interior (closure A) := hP3 hx
    simpa [hEq] using hx'

theorem P2_implies_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have hOpen : IsOpen A :=
    (Topology.P2_closed_iff_open hA_closed).1 hP2
  exact Topology.P1_of_open hOpen

theorem P1_iff_P2_of_closed_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosedInt : IsClosed (interior A)) :
    Topology.P1 A ↔ Topology.P2 A := by
  -- `closure (interior A)` collapses to `interior A` because this interior is closed.
  have hClosEq : closure (interior A) = interior A := hClosedInt.closure_eq
  constructor
  · intro hP1
    dsimp [Topology.P2] at *
    intro x hxA
    -- From `P1`, `x` lies in `closure (interior A) = interior A`.
    have hxIntA : x ∈ interior A := by
      have hxClos : x ∈ closure (interior A) := hP1 hxA
      simpa [hClosEq] using hxClos
    -- Re-interpret this membership in the desired interior.
    simpa [hClosEq, interior_interior] using hxIntA
  · intro hP2
    dsimp [Topology.P1] at *
    intro x hxA
    -- `P2` gives `x` in `interior (closure (interior A))`.
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    -- The interior is contained in the closure.
    have hIncl : interior (closure (interior A))
        ⊆ closure (interior A) := interior_subset
    exact hIncl hxInt

theorem P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  have hP3_open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_open hA_closed
  have hOpen_int : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  exact hP3_open.trans hOpen_int

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  simpa using (Topology.P123_univ (X := X)).1

theorem closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    closure A = closure (interior (closure A)) := by
  apply Set.Subset.antisymm
  ·
    have hSub : (A : Set X) ⊆ interior (closure A) := hP3
    simpa using (closure_mono hSub)
  ·
    have hSub : interior (closure A) ⊆ closure A := interior_subset
    have : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono hSub
    simpa [closure_closure] using this

theorem interior_closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  exact ⟨x, hx⟩

theorem P123_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  exact ⟨Topology.P1_empty (X := X), Topology.P2_empty (X := X), Topology.P3_empty (X := X)⟩

theorem closure_eq_closure_interior_of_open {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure A = closure (interior A) := by
  have hP2 : Topology.P2 A := Topology.P2_of_open hA
  exact Topology.closure_eq_closure_interior_of_P2 hP2

theorem P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hP3Clos
  dsimp [Topology.P3] at hP3Clos ⊢
  intro x hxA
  have hxClosure : x ∈ closure A :=
    (subset_closure : A ⊆ closure A) hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3Clos hxClosure
  simpa [closure_closure] using hxInt

theorem dense_iff_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ closure (A : Set X) = Set.univ := by
  classical
  constructor
  · intro hDense
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      exact hDense x
  · intro hEq
    intro x
    have : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [hEq] using this

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  simpa using (Topology.P123_univ (X := X)).2.2

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x _hxA
  -- `Dense` gives `closure A = univ`.
  have hCl : closure (A : Set X) = Set.univ :=
    (Topology.dense_iff_closure_eq_univ).1 hDense
  -- Hence `interior (closure A)` is `univ`, and the goal is immediate.
  have : x ∈ interior (closure (A : Set X)) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hCl, interior_univ] using this
  exact this

theorem interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    interior (closure (A : Set X)) = Set.univ := by
  have hCl : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ).1 hDense
  simpa [hCl, interior_univ]

theorem P3_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P3 (closure (A : Set X)) := by
  intro hDense
  have hCl : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ).1 hDense
  simpa [hCl] using (Topology.P3_univ (X := X))

theorem P2_of_P1_and_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpen : IsOpen (closure (interior A))) :
    Topology.P2 A := by
  dsimp [Topology.P2, Topology.P1] at *
  intro x hxA
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  have hIntEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  simpa [hIntEq] using hxCl

theorem P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2Clos
  dsimp [Topology.P3] at *
  intro x hxA
  -- `x` lies in the closure of `A`.
  have hxClos : x ∈ closure (A : Set X) :=
    (subset_closure : (A : Set X) ⊆ closure A) hxA
  -- Apply `P2` to `closure A`.
  have hxInt :
      x ∈ interior (closure (interior (closure (A : Set X)))) :=
    hP2Clos hxClos
  -- Relate the two interiors via the auxiliary lemma.
  have hIncl :
      interior (closure (interior (closure (A : Set X))))
        ⊆ interior (closure (A : Set X)) := by
    simpa using
      (Topology.interior_closure_interior_subset_interior_closure
        (A := closure (A : Set X)))
  exact hIncl hxInt

theorem P1_closure_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) : Topology.P1 (closure (A : Set X)) := by
  dsimp [Topology.P1]
  have hIncl : (closure A : Set X) ⊆ closure (interior (closure A)) := by
    -- First, an open set is contained in the interior of its closure.
    have hSub : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
    -- Taking closures preserves inclusions.
    exact closure_mono hSub
  exact hIncl

theorem P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure (A : Set X)) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.P1_closure (A := A) hP1

theorem closure_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    closure A = closure (interior (closure A)) := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
  exact Topology.closure_eq_closure_interior_closure_of_P3 hP3

theorem P3_implies_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A → Topology.P2 A := by
  intro hP3
  -- From `P3` and closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_closed_iff_open hA_closed).1 hP3
  -- For an open set, `P2` holds.
  exact Topology.P2_of_open hOpen

theorem closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.closure_interior_nonempty_of_P1 hP1 hA

theorem P3_union_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P2 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP2B
  have hP3B : Topology.P3 B := Topology.P2_implies_P3 hP2B
  exact Topology.P3_union hP3A hP3B

theorem P2_closure_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure (A : Set X)) := by
  have h : Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) :=
    Topology.P2_closure_iff_open_closure (A := A)
  exact (h.mpr hOpen)

theorem P2_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P2 (closure (A : Set X)) := by
  intro hDense
  -- `closure A` equals `univ` because `A` is dense.
  have hClosEq : closure (A : Set X) = Set.univ :=
    (Topology.dense_iff_closure_eq_univ).1 hDense
  -- Hence `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    simpa [hClosEq] using (isOpen_univ : IsOpen (Set.univ : Set X))
  -- Apply the equivalence `P2 (closure A) ↔ IsOpen (closure A)`.
  have hEquiv :
      Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) :=
    Topology.P2_closure_iff_open_closure (A := A)
  exact (hEquiv.mpr hOpen)

theorem P1_iff_P2_of_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior A))) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro hP1
    exact Topology.P2_of_P1_and_open_closure_interior hP1 hOpen
  · intro hP2
    exact Topology.P2_implies_P1 hP2

theorem P1_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hDense
  have hCl : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  simpa [hCl] using (Topology.P1_univ (X := X))

theorem P123_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpenUnion : IsOpen (A ∪ B : Set X) := hA.union hB
  exact Topology.P123_of_open hOpenUnion

theorem interior_closure_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (A : Set X))) = interior (closure (A : Set X)) := by
  simpa [closure_closure]

theorem P1_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P1_of_open hOpen

theorem interior_closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- The closure of `A ∩ B` is contained in the closure of `A`.
  have hA : interior (closure (A ∩ B : Set X)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (Set.inter_subset_left))
  -- The closure of `A ∩ B` is contained in the closure of `B`.
  have hB : interior (closure (A ∩ B : Set X)) ⊆ interior (closure B) :=
    interior_mono (closure_mono (Set.inter_subset_right))
  exact ⟨hA hx, hB hx⟩



theorem interior_closure_interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  exact interior_subset

theorem interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (A : Set X) := by
  -- First step: the interior of a set is contained in the set itself.
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  -- Second step: the closure operator is monotone.
  have h₂ : closure (interior A) ⊆ closure (A : Set X) := by
    apply closure_mono
    exact (interior_subset : interior A ⊆ A)
  -- Combining the two inclusions yields the desired result.
  exact Set.Subset.trans h₁ h₂

theorem P1_and_P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  exact ⟨Topology.P2_implies_P1 hP2, Topology.P2_implies_P3 hP2⟩

theorem P2_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P2_of_open hOpen

theorem interior_closure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hIncl : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have hSub : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact closure_mono hSub
      exact hIncl hxA
  | inr hxB =>
      have hIncl : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have hSub : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact closure_mono hSub
      exact hIncl hxB

theorem closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hLeft :
      closure (interior (A ∩ B : Set X)) ⊆ closure (interior A) := by
    apply closure_mono
    have : interior (A ∩ B : Set X) ⊆ interior A := by
      apply interior_mono
      exact Set.inter_subset_left
    exact this
  have hRight :
      closure (interior (A ∩ B : Set X)) ⊆ closure (interior B) := by
    apply closure_mono
    have : interior (A ∩ B : Set X) ⊆ interior B := by
      apply interior_mono
      exact Set.inter_subset_right
    exact this
  exact ⟨hLeft hx, hRight hx⟩

theorem P3_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior A))) := by
  have hP2 : Topology.P2 (interior (closure (interior A))) :=
    Topology.P2_interior_closure_interior A
  exact Topology.P2_implies_P3 hP2

theorem P123_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) ∧
    Topology.P2 (interior (closure A)) ∧
    Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using Topology.P123_of_open hOpen

theorem closure_subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure A ⊆ closure (interior A) := by
  simpa [closure_closure] using (closure_mono hP1)

theorem closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hIncl : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have hSub : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact hSub
      exact hIncl hA
  | inr hB =>
      have hIncl : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have hSub : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact hSub
      exact hIncl hB

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure (A : Set X)) := by
  intro hP3
  -- Unfold definitions of `P3` and `P1`.
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  intro x hxCl
  -- Use monotonicity of `closure` with the inclusion given by `hP3`.
  have hIncl : closure (A : Set X) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    exact hP3
  exact hIncl hxCl

theorem closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    closure (interior (closure (A : Set X))) = Set.univ := by
  have hInt : interior (closure (A : Set X)) = Set.univ :=
    Topology.interior_closure_eq_univ_of_dense (A := A) hDense
  calc
    closure (interior (closure (A : Set X)))
        = closure (Set.univ : Set X) := by
          simpa [hInt]
    _ = (Set.univ : Set X) := by
          simpa

theorem P2_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  have h := Topology.P123_inter_open (A := A) (B := B) hA hB
  exact h.2.1

theorem closure_interior_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    closure (interior A) = closure (interior (closure A)) := by
  calc
    closure (interior A)
        = closure A := (Topology.closure_eq_closure_interior_of_P2 (A := A) hP2).symm
    _ = closure (interior (closure A)) :=
      Topology.closure_eq_closure_interior_closure_of_P2 (A := A) hP2

theorem interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A := by
  exact interior_mono (Set.diff_subset)

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) := by
  exact interior_mono (closure_mono hAB)

theorem dense_of_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = Set.univ → Dense (A : Set X) := by
  intro hInt x
  -- Since `interior (closure A) = univ`, every point lies in this interior.
  have hx_int : (x : X) ∈ interior (closure (A : Set X)) := by
    have : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [hInt] using this
  -- The interior is contained in the closure, yielding the desired density.
  exact (interior_subset : interior (closure (A : Set X)) ⊆ closure (A : Set X)) hx_int

theorem interior_closure_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    interior (closure A) ⊆ A := by
  -- Since `A` is closed, `closure A = A`.
  simpa [hA_closed.closure_eq] using
    (interior_subset : interior (closure A) ⊆ closure A)

theorem dense_closure_iff_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure (A : Set X)) ↔ Dense (A : Set X) := by
  classical
  constructor
  · intro hDenseClos
    -- Translate density of `closure A` into a closure equality.
    have hEq₁ : closure (closure (A : Set X)) = (Set.univ : Set X) :=
      (Topology.dense_iff_closure_eq_univ).1 hDenseClos
    -- Use `closure_closure` to rewrite.
    have hEq₂ : closure (A : Set X) = (Set.univ : Set X) := by
      simpa [closure_closure] using hEq₁
    -- Re‐encode as density of `A`.
    exact (Topology.dense_iff_closure_eq_univ).2 hEq₂
  · intro hDenseA
    -- Translate density of `A` into a closure equality.
    have hEq₁ : closure (A : Set X) = (Set.univ : Set X) :=
      (Topology.dense_iff_closure_eq_univ).1 hDenseA
    -- Apply `closure_closure` to obtain the desired equality.
    have hEq₂ : closure (closure (A : Set X)) = (Set.univ : Set X) := by
      simpa [closure_closure] using hEq₁
    -- Re‐encode as density of `closure A`.
    exact (Topology.dense_iff_closure_eq_univ).2 hEq₂

theorem closure_interior_subset_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure (interior A))) := by
  -- First, show `interior A ⊆ interior (closure (interior A))`.
  have hInt : interior A ⊆ interior (closure (interior A)) := by
    have h' : interior (interior A) ⊆ interior (closure (interior A)) := by
      -- `interior` is monotone with respect to set inclusion.
      exact
        interior_mono
          (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using h'
  -- Taking closures preserves inclusions.
  exact closure_mono hInt

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (A : Set X) := by
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem P3_of_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = Set.univ → Topology.P3 A := by
  intro hInt
  -- From the equality of interiors, infer density of `A`.
  have hDense : Dense (A : Set X) :=
    Topology.dense_of_interior_closure_eq_univ (A := A) hInt
  -- Density implies property `P3`.
  exact Topology.P3_of_dense (X := X) hDense

theorem closure_interior_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem interior_closure_interior_eq_interior_of_closed_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosedInt : IsClosed (interior (A : Set X))) :
    interior (closure (interior (A : Set X))) = interior (A : Set X) := by
  have h : closure (interior (A : Set X)) = interior (A : Set X) :=
    hClosedInt.closure_eq
  simpa [h, interior_interior]

theorem P3_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  have h := Topology.P123_inter_open (A := A) (B := B) hA hB
  exact h.2.2

theorem interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B : Set X)) =
      interior (closure (A : Set X) ∪ closure (B : Set X)) := by
  simpa [closure_union]

theorem dense_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ interior (closure (A : Set X)) = Set.univ := by
  constructor
  · intro hDense
    exact Topology.interior_closure_eq_univ_of_dense (A := A) hDense
  · intro hInt
    exact Topology.dense_of_interior_closure_eq_univ (A := A) hInt

theorem dense_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Dense (A : Set X) := by
  intro hDenseInt x
  have hx : (x : X) ∈ closure (interior (A : Set X)) := hDenseInt x
  have hIncl : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  exact hIncl hx

theorem interior_closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆
      interior (closure (A : Set X)) := by
  -- `A \ B` is contained in `A`.
  have hSub : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- The `closure` operator preserves inclusions.
  have hClos : closure (A \ B : Set X) ⊆ closure (A : Set X) :=
    closure_mono hSub
  -- Taking interiors preserves inclusions as well.
  exact interior_mono hClos

theorem interior_closure_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior (A : Set X) := by
  simpa [hA_closed.closure_eq]

theorem interior_closure_inter_eq_of_closed_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP3A : Topology.P3 A) (hP3B : Topology.P3 B) :
    interior (closure (A ∩ B : Set X)) = A ∩ B := by
  -- `A ∩ B` is closed.
  have hClosedInter : IsClosed (A ∩ B : Set X) := hA_closed.inter hB_closed
  -- `A ∩ B` satisfies `P3`.
  have hP3Inter : Topology.P3 (A ∩ B : Set X) :=
    Topology.P3_inter_closed hA_closed hB_closed hP3A hP3B
  -- Hence `A ∩ B` is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) :=
    (Topology.P3_closed_iff_open hClosedInter).1 hP3Inter
  -- The interior of an open set is the set itself.
  have hIntEq : interior (A ∩ B : Set X) = A ∩ B := hOpenInter.interior_eq
  -- The closure of a closed set is the set itself.
  have hClosEq : closure (A ∩ B : Set X) = A ∩ B := hClosedInter.closure_eq
  -- Combine the two equalities to obtain the desired statement.
  simpa [hClosEq, hIntEq]

theorem interior_closure_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- `interior` is monotone with respect to set inclusion.
  have hA :
      interior (closure (A : Set X) ∩ closure (B : Set X))
        ⊆ interior (closure (A : Set X)) := by
    apply interior_mono
    exact Set.inter_subset_left
  have hB :
      interior (closure (A : Set X) ∩ closure (B : Set X))
        ⊆ interior (closure (B : Set X)) := by
    apply interior_mono
    exact Set.inter_subset_right
  exact ⟨hA hx, hB hx⟩

theorem subset_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    (A : Set X) ⊆ closure (interior (closure A)) := by
  -- From `P1`, we already know `A ⊆ closure (interior A)`.
  have h₁ : (A : Set X) ⊆ closure (interior A) := hP1
  -- And `closure (interior A) ⊆ closure (interior (closure A))` by monotonicity.
  have h₂ :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  -- Combining the two inclusions yields the desired result.
  exact Set.Subset.trans h₁ h₂

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  exact Topology.closure_interior_subset_closure_interior_closure_interior (A := A)

theorem closure_interior_eq_self_of_closed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = A := by
  -- From `P3` and closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A := (Topology.P3_closed_iff_open hClosed).1 hP3
  -- Hence the interior of `A` is `A` itself.
  have hInt : interior A = A := hOpen.interior_eq
  calc
    closure (interior A) = closure A := by
      simpa [hInt]
    _ = A := hClosed.closure_eq

theorem P2_closure_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hP3
  exact
    (Topology.P3_implies_P2_of_closed
        (A := closure (A : Set X)) isClosed_closure) hP3

theorem closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (A : Set X))) ⊆ closure A := by
  -- `interior (closure A)` is contained in `closure A`.
  have h₁ : interior (closure (A : Set X)) ⊆ closure A := interior_subset
  -- The closure operator preserves inclusions.
  have h₂ :
      closure (interior (closure (A : Set X)))
        ⊆ closure (closure (A : Set X)) :=
    closure_mono h₁
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h₂

theorem P2_interior_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P2_iff_P3_of_open (A := interior A) hOpen)

theorem closure_interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- `interior (A \ B)` is contained in `interior A`.
  have h : interior (A \ B : Set X) ⊆ interior A :=
    Topology.interior_diff_subset (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono h

theorem closure_inter_subset_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : closure (A ∩ B : Set X) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : closure (A ∩ B : Set X) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact ⟨hA hx, hB hx⟩

theorem closure_eq_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure A = closure (interior (closure A)) := by
  apply Set.Subset.antisymm
  ·
    -- `A ⊆ closure (interior (closure A))` by `P1`.
    have hSub : (A : Set X) ⊆ closure (interior (closure A)) :=
      Topology.subset_closure_interior_closure_of_P1 hP1
    -- Taking closures gives the required inclusion.
    have hClos : closure A ⊆ closure (closure (interior (closure A))) :=
      closure_mono hSub
    simpa [closure_closure] using hClos
  ·
    exact Topology.closure_interior_closure_subset_closure (A := A)

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  -- First, translate `P2` into openness for a closed set.
  have hP2_open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_open (A := A) hA_closed
  -- Next, characterize openness via the interior.
  have hOpen_int : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  exact hP2_open.trans hOpen_int

theorem closure_interior_eq_self_of_closed_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP1 : Topology.P1 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  simpa using
    ((Topology.P1_closed_iff_closure_interior_eq (A := A) hClosed).1 hP1)

theorem interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X)) ⊆
      closure (interior (closure (A : Set X))) := by
  intro x hx
  exact subset_closure hx

theorem interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  intro x hxInt
  have hxA : x ∈ (A : Set X) := interior_subset hxInt
  exact (subset_closure : (A : Set X) ⊆ closure A) hxA

theorem closure_interior_closure_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure (A : Set X)))) =
      closure (interior (closure (A : Set X))) := by
  simpa [closure_closure]

theorem interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure (A : Set X)) := by
  apply Set.Subset.antisymm
  ·
    have h :
        interior (closure (interior (closure (A : Set X))))
          ⊆ interior (closure (closure (A : Set X))) :=
      (Topology.interior_closure_interior_subset_interior_closure
        (A := closure (A : Set X)))
    simpa [closure_closure] using h
  ·
    have hSub :
        interior (closure (A : Set X))
          ⊆ closure (interior (closure (A : Set X))) :=
      (subset_closure :
        interior (closure (A : Set X)) ⊆
          closure (interior (closure (A : Set X))))
    have h :
        interior (interior (closure (A : Set X)))
          ⊆ interior (closure (interior (closure (A : Set X)))) :=
      interior_mono hSub
    simpa [interior_interior] using h

theorem closure_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  -- From `interior_closure_interior_closure`, the two interiors coincide.
  have h := Topology.interior_closure_interior_closure (A := A)
  simpa [h]

theorem P1_interior_iff_P3_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P1_iff_P3_of_open (A := interior A) hOpen)

theorem P1_iff_closure_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact Topology.closure_subset_closure_interior_of_P1 (A := A) hP1
  · intro hSub
    dsimp [Topology.P1] at *
    intro x hxA
    have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
    exact hSub hxCl

theorem dense_inter_open_nonempty
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hDense : Dense (A : Set X)) (hU_open : IsOpen U)
    (hU_nonempty : (U : Set X).Nonempty) :
    (A ∩ U : Set X).Nonempty := by
  classical
  -- Choose a point `x` in the nonempty open set `U`.
  rcases hU_nonempty with ⟨x, hxU⟩
  -- Density provides that `x` lies in the closure of `A`.
  have hx_closure : x ∈ closure (A : Set X) := hDense x
  -- The characterization of the closure via open neighbourhoods
  -- yields a point of `A` inside `U`.
  have hIntersect : (U ∩ A : Set X).Nonempty :=
    (mem_closure_iff).1 hx_closure U hU_open hxU
  -- Reorder the intersection to match the goal.
  simpa [Set.inter_comm] using hIntersect

theorem interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure (interior A)) := by
  -- First, note the basic inclusion `interior A ⊆ closure (interior A)`.
  have h :
      interior (interior A) ⊆ interior (closure (interior A)) := by
    apply interior_mono
    exact (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  -- Rewrite `interior (interior A)` as `interior A` to obtain the goal.
  simpa [interior_interior] using h

theorem closure_interior_eq_closure_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure (A : Set X) := by
  simpa using
    (Topology.closure_eq_closure_interior_of_open (A := A) hA).symm

theorem interior_closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B : Set X))) ⊆
      interior (closure (interior A)) ∩
        interior (closure (interior B)) := by
  intro x hx
  have hA :
      interior (closure (interior (A ∩ B : Set X))) ⊆
        interior (closure (interior A)) := by
    apply interior_mono
    have hSub_int : interior (A ∩ B : Set X) ⊆ interior A := by
      apply interior_mono
      exact Set.inter_subset_left
    exact closure_mono hSub_int
  have hB :
      interior (closure (interior (A ∩ B : Set X))) ⊆
        interior (closure (interior B)) := by
    apply interior_mono
    have hSub_int : interior (A ∩ B : Set X) ⊆ interior B := by
      apply interior_mono
      exact Set.inter_subset_right
    exact closure_mono hSub_int
  exact ⟨hA hx, hB hx⟩

theorem interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A : Set X))) ∪
        interior (closure (interior (B : Set X))) ⊆
      interior (closure (interior (A ∪ B : Set X))) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hIncl :
          interior (closure (interior (A : Set X)))
            ⊆ interior (closure (interior (A ∪ B : Set X))) := by
        apply interior_mono
        have hSub :
            closure (interior (A : Set X)) ⊆
              closure (interior (A ∪ B : Set X)) := by
          apply closure_mono
          have hIntSub :
              interior (A : Set X) ⊆ interior (A ∪ B : Set X) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact hIntSub
        exact hSub
      exact hIncl hA
  | inr hB =>
      have hIncl :
          interior (closure (interior (B : Set X)))
            ⊆ interior (closure (interior (A ∪ B : Set X))) := by
        apply interior_mono
        have hSub :
            closure (interior (B : Set X)) ⊆
              closure (interior (A ∪ B : Set X)) := by
          apply closure_mono
          have hIntSub :
              interior (B : Set X) ⊆ interior (A ∪ B : Set X) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact hIntSub
        exact hSub
      exact hIncl hB

theorem interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A` is contained in `interior (A ∪ B)`
      have hIncl : interior (A : Set X) ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hIncl hxA
  | inr hxB =>
      -- `interior B` is contained in `interior (A ∪ B)`
      have hIncl : interior (B : Set X) ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hIncl hxB

theorem P2_closure_interior_iff_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) ↔
      Topology.P3 (closure (interior (A : Set X))) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P2_iff_P3_of_closed
      (A := closure (interior (A : Set X))) hClosed)



theorem P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = Set.univ) :
    Topology.P3 A := by
  -- From the closure equality, deduce density of `A`.
  have hDense : Dense (A : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).2 h
  -- Density implies `P3`.
  exact Topology.P3_of_dense (X := X) hDense

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 A := by
  intro hDenseInt
  have hDenseA : Dense (A : Set X) :=
    Topology.dense_of_dense_interior (A := A) hDenseInt
  exact Topology.P3_of_dense (X := X) (A := A) hDenseA

theorem P1_interior_iff_P2_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P1_iff_P2_of_open (A := interior A) hOpen)

theorem P1_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h] using this

theorem dense_of_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (A : Set X))) = Set.univ →
      Dense (A : Set X) := by
  intro hUniv
  -- `closure (A)` contains the dense set `interior (closure A)`,
  -- whose closure is `univ` by hypothesis.
  have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    have hIncl :
        closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
      Topology.closure_interior_closure_subset_closure (A := A)
    simpa [hUniv] using hIncl
  -- Hence `closure A = univ`.
  have hEq : closure (A : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    · exact hSub
  -- Translate this equality into density of `A`.
  exact (Topology.dense_iff_closure_eq_univ (A := A)).2 hEq

theorem closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    have h₁ : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (A := A)
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    simpa using h₂

theorem P2_union_P3 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP2A hP3B
  have h : Topology.P3 (B ∪ A) :=
    Topology.P3_union_P2 (A := B) (B := A) hP3B hP2A
  simpa [Set.union_comm] using h

theorem interior_closure_iUnion_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, interior (closure (A i : Set X))) ⊆
      interior (closure (⋃ i, A i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `interior` and `closure` are both monotone, allowing us to enlarge the set.
  have hIncl :
      interior (closure (A i : Set X)) ⊆
        interior (closure (⋃ j, A j : Set X)) := by
    apply interior_mono
    have hSub : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono hSub
  exact hIncl hx_i

theorem closure_interior_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  have hSub :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  simpa [hA_closed.closure_eq] using hSub

theorem dense_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = Set.univ) :
    Dense (A : Set X) := by
  classical
  -- `closure (interior A)` is contained in `closure A`.
  have hSub : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    Topology.closure_interior_subset_closure (A := A)
  -- Thus `closure A` coincides with `univ`.
  have hClos : closure (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · have hUniv : (Set.univ : Set X) ⊆ closure (A : Set X) := by
        simpa [h] using hSub
      exact hUniv
  -- Translate the closure equality into density.
  exact (Topology.dense_iff_closure_eq_univ (A := A)).2 hClos

theorem P2_closure_interior_iff_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P2_closed_iff_open
      (A := closure (interior (A : Set X))) hClosed)

theorem closure_interior_eq_self_of_closed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  -- From `P2` and closedness of `A`, we have `interior A = A`.
  have hIntEq : interior A = A :=
    (Topology.P2_closed_iff_interior_eq (A := A) hClosed).1 hP2
  calc
    closure (interior A) = closure A := by
      simpa [hIntEq]
    _ = A := hClosed.closure_eq

theorem P1_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P1 A := by
  intro hDenseInt
  -- Density gives `closure (interior A) = univ`.
  have hClos :
      closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (A : Set X))).1 hDenseInt
  -- Apply the existing lemma.
  exact Topology.P1_of_closure_interior_eq_univ (A := A) hClos

theorem P1_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 A → Topology.P1 (A ∩ B) := by
  intro hP1
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `x` lies in the closure of `interior A`.
  have hxClA : x ∈ closure (interior A) := hP1 hxA
  -- We show that `x` belongs to the closure of `interior (A ∩ B)`.
  -- To this end, we establish a more general inclusion.
  have hIncl :
      (closure (interior A) ∩ B) ⊆ closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyClA, hyB⟩
    -- Characterize membership in a closure via neighbourhoods.
    have : y ∈ closure (interior (A ∩ B)) := by
      -- Use the neighbourhood formulation of `closure`.
      apply (mem_closure_iff).2
      intro U hU_open hyU
      -- Intersect the neighbourhood with `B`, which is open.
      have hU_B_open : IsOpen (U ∩ B) := hU_open.inter hOpenB
      have hyU_B : y ∈ U ∩ B := ⟨hyU, hyB⟩
      -- From `y ∈ closure (interior A)` we obtain a point of `interior A`
      -- meeting `U ∩ B`.
      have hNonempty :
          ((U ∩ B) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hU_B_open hyU_B
      rcases hNonempty with ⟨z, ⟨⟨hzU, hzB⟩, hzIntA⟩⟩
      -- Identify the interior of the intersection using openness of `B`.
      have hIntEq :
          interior (A ∩ B : Set X) = interior A ∩ B := by
        simpa [hOpenB.interior_eq] using interior_inter
      -- The point `z` lies in `U ∩ interior (A ∩ B)`.
      have hzIntAB : z ∈ interior (A ∩ B) := by
        have : z ∈ interior A ∩ B := ⟨hzIntA, hzB⟩
        simpa [hIntEq] using this
      exact ⟨z, ⟨hzU, hzIntAB⟩⟩
    exact this
  -- Apply the inclusion to our point `x`.
  have : x ∈ closure (interior (A ∩ B)) :=
    hIncl ⟨hxClA, hxB⟩
  exact this

theorem isOpen_of_closed_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 A) :
    IsOpen (A : Set X) := by
  exact ((Topology.P2_closed_iff_open (A := A) hClosed).1 hP2)

theorem dense_interior_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) ↔
      interior (closure (interior (A : Set X))) = Set.univ := by
  simpa using
    (Topology.dense_iff_interior_closure_eq_univ
      (A := interior (A : Set X)))

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 A := by
  intro hDenseInt
  -- From density, obtain `interior (closure (interior A)) = univ`.
  have hUniv :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) :=
    (Topology.dense_interior_iff_interior_closure_interior_eq_univ
        (A := A)).1 hDenseInt
  -- Unfold `P2` and finish the proof.
  dsimp [Topology.P2]
  intro x _hxA
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hUniv] using hx_univ



theorem closure_interior_eq_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure (interior A) = closure (interior (closure A)) := by
  apply Set.Subset.antisymm
  ·
    exact
      Topology.closure_interior_subset_closure_interior_closure (A := A)
  ·
    have hInt :
        interior (closure A) = interior (closure (interior A)) :=
      Topology.interior_closure_eq_interior_closure_interior_of_P1
        (A := A) hP1
    have hEq :
        closure (interior (closure A)) = closure (interior A) := by
      calc
        closure (interior (closure A))
            = closure (interior (closure (interior A))) := by
              simpa [hInt]
        _ = closure (interior A) := by
              simpa using
                (Topology.closure_interior_closure_interior_eq_closure_interior
                  (A := A))
    simpa [hEq] using (Set.Subset.rfl)

theorem isClosed_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior A)) := by
  simpa using (isClosed_closure : IsClosed (closure (interior A)))

theorem P1_union_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P2 B → Topology.P1 (A ∪ B) := by
  intro hP1A hP2B
  have hP1B : Topology.P1 B := Topology.P2_implies_P1 hP2B
  exact Topology.P1_union hP1A hP1B

theorem dense_iff_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ closure (interior (closure (A : Set X))) = Set.univ := by
  constructor
  · intro hDense
    exact
      Topology.closure_interior_closure_eq_univ_of_dense (A := A) hDense
  · intro hEq
    exact
      Topology.dense_of_closure_interior_closure_eq_univ (A := A) hEq

theorem interior_closure_iInter_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    interior (closure (⋂ i, A i : Set X)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- Show that `x` belongs to `interior (closure (A i))` for every `i`.
  have hx_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- `closure` is monotone with respect to set inclusion.
    have h_closure_subset :
        closure (⋂ j, A j : Set X) ⊆ closure (A i) := by
      apply closure_mono
      intro y hy
      -- Membership in the intersection yields membership in each component.
      exact (Set.mem_iInter.1 hy) i
    -- Taking interiors preserves inclusions.
    have h_interior_subset :
        interior (closure (⋂ j, A j : Set X)) ⊆
          interior (closure (A i)) :=
      interior_mono h_closure_subset
    exact h_interior_subset hx
  -- Assemble the pointwise condition into membership in the intersection.
  exact Set.mem_iInter.2 hx_i

theorem closure_interior_iUnion_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, closure (interior (A i : Set X))) ⊆
      closure (interior (⋃ i, A i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hIncl :
      closure (interior (A i : Set X)) ⊆
        closure (interior (⋃ j, A j : Set X)) := by
    apply closure_mono
    have hInt :
        interior (A i : Set X) ⊆ interior (⋃ j, A j : Set X) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact hInt
  exact hIncl hx_i

theorem interior_iUnion_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, interior (A i : Set X)) ⊆ interior (⋃ i, A i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hIncl :
      interior (A i : Set X) ⊆ interior (⋃ j, A j : Set X) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hIncl hx_i

theorem closure_interior_iInter_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    closure (interior (⋂ i, A i : Set X)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- Show that `x ∈ closure (interior (A i))` for every index `i`.
  have hx_i : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- `interior` is monotone with respect to set inclusion.
    have hSub_int : interior (⋂ j, A j : Set X) ⊆ interior (A i) := by
      apply interior_mono
      -- The intersection is contained in each component.
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Taking closures preserves inclusions.
    have hSub_clos :
        closure (interior (⋂ j, A j : Set X)) ⊆
          closure (interior (A i)) :=
      closure_mono hSub_int
    exact hSub_clos hx
  -- Assemble the pointwise membership into the intersection.
  exact Set.mem_iInter.2 hx_i

theorem interior_closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (interior (B : Set X))) := by
  -- First, `interior` is monotone with respect to set inclusion.
  have hInt : interior (A : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  -- Taking closures preserves inclusions.
  have hClos :
      closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) :=
    closure_mono hInt
  -- Finally, `interior` is again monotone.
  exact interior_mono hClos

theorem P3_closure_interior_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) →
      Topology.P3 (closure (interior (A : Set X))) := by
  intro hDenseInt
  simpa using
    (Topology.P3_closure_of_dense (A := interior (A : Set X)) hDenseInt)

theorem P1_sUnion {X : Type*} [TopologicalSpace X] (A : Set (Set X))
    (h : ∀ B, B ∈ A → Topology.P1 (B : Set X)) :
    Topology.P1 (⋃₀ A) := by
  classical
  dsimp [Topology.P1] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBA, hxB⟩
  have hPB : (B : Set X) ⊆ closure (interior B) := h B hBA
  have hx_cl : x ∈ closure (interior B) := hPB hxB
  have hSub : (B : Set X) ⊆ ⋃₀ A := Set.subset_sUnion_of_mem hBA
  have hIntSub : interior B ⊆ interior (⋃₀ A) := by
    apply interior_mono
    exact hSub
  have h_mono : closure (interior B) ⊆ closure (interior (⋃₀ A)) :=
    closure_mono hIntSub
  exact h_mono hx_cl

theorem P2_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hDenseInt
  -- `Dense (interior A)` implies `Dense A`.
  have hDenseA : Dense (A : Set X) :=
    Topology.dense_of_dense_interior (A := A) hDenseInt
  -- Apply the existing lemma for dense sets.
  exact Topology.P2_closure_of_dense (A := A) hDenseA

theorem P2_sUnion {X : Type*} [TopologicalSpace X] (A : Set (Set X))
    (h : ∀ B, B ∈ A → Topology.P2 (B : Set X)) :
    Topology.P2 (⋃₀ A) := by
  classical
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBA, hxB⟩
  have hPB : (B : Set X) ⊆ interior (closure (interior B)) := h B hBA
  have hxInt : x ∈ interior (closure (interior B)) := hPB hxB
  have hIncl :
      interior (closure (interior B)) ⊆
        interior (closure (interior (⋃₀ A))) := by
    apply interior_mono
    have : closure (interior B) ⊆ closure (interior (⋃₀ A)) := by
      apply closure_mono
      have : interior (B : Set X) ⊆ interior (⋃₀ A) := by
        apply interior_mono
        exact Set.subset_sUnion_of_mem hBA
      exact this
    exact this
  exact hIncl hxInt

theorem P1_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) := by
  have hP1B : Topology.P1 B := Topology.P1_of_open hOpenB
  exact Topology.P1_union hP1A hP1B

theorem P3_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- `B` is open, hence satisfies `P3`.
  have hP3B : Topology.P3 (B : Set X) := Topology.P3_of_open hOpenB
  -- Combine the two `P3` properties.
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B

theorem closure_union_eq_univ_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDense : Dense (A : Set X)) :
    closure (A ∪ B : Set X) = (Set.univ : Set X) := by
  classical
  -- From density we know `closure A = univ`.
  have hClA : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  -- Compute the closure of the union using distributivity over `closure`.
  calc
    closure (A ∪ B : Set X)
        = closure (A : Set X) ∪ closure (B : Set X) := by
          simpa [closure_union]
    _ = (Set.univ : Set X) ∪ closure (B : Set X) := by
          simpa [hClA]
    _ = (Set.univ : Set X) := by
          simpa [Set.univ_union]

theorem interior_iInter_subset_interiors
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    interior (⋂ i, A i : Set X) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- For each `i`, `x` lies in `interior (A i)`.
  have hx_i : ∀ i, x ∈ interior (A i) := by
    intro i
    -- The intersection is contained in each component.
    have hSub : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` gives the desired inclusion.
    have hInt : interior (⋂ j, A j : Set X) ⊆ interior (A i) :=
      interior_mono hSub
    exact hInt hx
  -- Assemble the pointwise condition into membership in the intersection.
  exact Set.mem_iInter.2 hx_i

theorem interior_inter_eq_self_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using hOpen.interior_eq

theorem closure_interior_closure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  -- From `A ⊆ B` we obtain `closure A ⊆ closure B`.
  have h₁ : closure (A : Set X) ⊆ closure (B : Set X) :=
    closure_mono hAB
  -- Taking interiors preserves this inclusion.
  have h₂ :
      interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) :=
    interior_mono h₁
  -- Finally, closures are monotone, giving the desired result.
  exact closure_mono h₂

theorem dense_union_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) :
    Dense (A ∪ B : Set X) := by
  -- Via the existing lemma, the closure of the union is the whole space.
  have hClosUnion :
      closure (A ∪ B : Set X) = (Set.univ : Set X) :=
    Topology.closure_union_eq_univ_of_dense_left
      (A := A) (B := B) hDenseA
  -- Translate the closure equality back into density.
  exact
    (Topology.dense_iff_closure_eq_univ (A := A ∪ B)).2 hClosUnion

theorem dense_union_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseB : Dense (B : Set X)) :
    Dense (A ∪ B : Set X) := by
  simpa [Set.union_comm] using
    (Topology.dense_union_left (A := B) (B := A) hDenseB)

theorem P3_union_of_dense_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) :
    Topology.P3 (A ∪ B) := by
  have hDenseUnion : Dense (A ∪ B : Set X) :=
    Topology.dense_union_left (A := A) (B := B) hDenseA
  exact Topology.P3_of_dense (A := A ∪ B) hDenseUnion

theorem P3_union_of_dense_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseB : Dense (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P3_union_of_dense_left (A := B) (B := A) hDenseB)

theorem closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure (A : Set X) := by
  -- The set difference `A \ B` is contained in `A`.
  have hSub : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Use the monotonicity of `closure` to lift the inclusion.
  exact closure_mono hSub

theorem isOpen_of_closed_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsOpen A := by
  exact (Topology.P3_closed_iff_open hA_closed).1 hP3

theorem dense_interior_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) ↔
      closure (interior (A : Set X)) = Set.univ := by
  simpa using
    (dense_iff_closure_eq_univ (A := interior (A : Set X)))

theorem P1_iff_empty_of_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = ∅) :
    Topology.P1 A ↔ A = ∅ := by
  constructor
  · intro hP1
    have hSub : (A : Set X) ⊆ (∅ : Set X) := by
      intro x hxA
      have hx : x ∈ closure (interior A) := hP1 hxA
      simpa [hInt, closure_empty] using hx
    have hEq : A = (∅ : Set X) := by
      apply Set.Subset.antisymm hSub
      exact Set.empty_subset _
    exact hEq
  · intro hA
    simpa [hA] using (Topology.P1_empty (X := X))

theorem dense_iUnion_of_dense
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) (i₀ : ι)
    (hDense : Dense (A i₀)) :
    Dense (⋃ i, A i) := by
  classical
  intro x
  -- `hDense` tells us that `x` lies in the closure of `A i₀`.
  have hx : x ∈ closure (A i₀ : Set X) := hDense x
  -- Since `A i₀ ⊆ ⋃ i, A i`, the closures satisfy the analogous inclusion.
  have hSub : (A i₀ : Set X) ⊆ ⋃ i, A i := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i₀, hy⟩
  have hClosSub :
      closure (A i₀ : Set X) ⊆ closure (⋃ i, A i : Set X) :=
    closure_mono hSub
  -- Conclude that `x` lies in the desired closure.
  exact hClosSub hx

theorem interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (interior A) := by
  exact (subset_closure : interior (A : Set X) ⊆ closure (interior A))

theorem interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  classical
  constructor
  · intro hInt
    -- `interior (closure A)` is contained in `closure A`.
    have hSub : interior (closure (A : Set X)) ⊆ closure (A : Set X) :=
      interior_subset
    -- Using `hInt`, we obtain `univ ⊆ closure A`.
    have hLeft : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      simpa [hInt] using hSub
    -- Trivially, `closure A ⊆ univ`.
    have hRight : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro _ _; trivial
    exact Set.Subset.antisymm hRight hLeft
  · intro hClos
    -- Rewrite the left‐hand side using `hClos` and simplify.
    simpa [hClos, interior_univ]

theorem interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure A) := by
  -- The inclusion `A ⊆ closure A` is basic.
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  -- Monotonicity of `interior` yields the desired inclusion.
  exact interior_mono hSub

theorem closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior (A : Set X) = ∅ := by
  constructor
  · intro h
    -- Since `interior A ⊆ closure (interior A)`, the hypothesis forces `interior A = ∅`.
    have hSub : interior (A : Set X) ⊆ (∅ : Set X) := by
      have : interior (A : Set X) ⊆ closure (interior (A : Set X)) :=
        subset_closure
      simpa [h] using this
    exact
      (Set.Subset.antisymm hSub (Set.empty_subset _))
  · intro h
    simpa [h, closure_empty]

theorem P2_iff_subset_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (A : Set X) ⊆ interior (closure (interior A)) := by
  rfl

theorem P1_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (A : Set X)))) := by
  -- `interior (closure A)` is open.
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- Apply the existing lemma for the closure of an open set.
  exact
    Topology.P1_closure_of_open
      (A := interior (closure (A : Set X))) hOpen

theorem closure_inter_interior_subset_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `A ∩ interior B` is contained in `A`, hence its closure is contained in `closure A`.
  have hA : closure (A ∩ interior B : Set X) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ interior B : Set X) ⊆ A)
  -- Likewise, `A ∩ interior B` is contained in `B`, so its closure is contained in `closure B`.
  have hB : closure (A ∩ interior B : Set X) ⊆ closure B := by
    have hSub : (A ∩ interior B : Set X) ⊆ B := by
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact closure_mono hSub
  exact ⟨hA hx, hB hx⟩

theorem nonempty_of_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro hInt
  rcases hInt with ⟨x, hxInt⟩
  have hxCl : x ∈ closure (A : Set X) :=
    (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hxInt
  -- Apply the neighborhood characterization of `closure` with the open set `univ`.
  have hNonempty : ((Set.univ : Set X) ∩ A).Nonempty :=
    (mem_closure_iff).1 hxCl Set.univ isOpen_univ (by
      -- `x` trivially belongs to `univ`.
      trivial)
  simpa [Set.inter_univ] using hNonempty

theorem P3_sUnion {X : Type*} [TopologicalSpace X] (A : Set (Set X))
    (h : ∀ B, B ∈ A → Topology.P3 (B : Set X)) :
    Topology.P3 (⋃₀ A) := by
  classical
  dsimp [Topology.P3] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBA, hxB⟩
  have hx_in : x ∈ interior (closure (B : Set X)) := h B hBA hxB
  have hIncl : interior (closure (B : Set X)) ⊆
      interior (closure (⋃₀ A)) := by
    apply interior_mono
    have hSub : (B : Set X) ⊆ ⋃₀ A :=
      Set.subset_sUnion_of_mem hBA
    exact closure_mono hSub
  exact hIncl hx_in

theorem P2_closure_interior_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (closure (interior (A : Set X))) := by
  have hEquiv :
      Topology.P2 (closure (interior (A : Set X))) ↔
        IsOpen (closure (interior (A : Set X))) :=
    Topology.P2_closure_interior_iff_open_closure_interior (A := A)
  exact (hEquiv.mpr hOpen)

theorem P3_iff_empty_of_empty_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (closure (A : Set X)) = ∅) :
    Topology.P3 A ↔ A = ∅ := by
  classical
  constructor
  · intro hP3
    -- From `P3`, we have `A ⊆ interior (closure A)`.
    have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    -- But this interior is empty by hypothesis, hence `A ⊆ ∅`.
    have hSubEmpty : (A : Set X) ⊆ (∅ : Set X) := by
      simpa [hInt] using hSub
    -- Conclude that `A = ∅`.
    have hEq : (A : Set X) = (∅ : Set X) := by
      apply Set.Subset.antisymm hSubEmpty
      exact Set.empty_subset _
    simpa using hEq
  · intro hA
    -- The empty set satisfies `P3`.
    simpa [hA] using (Topology.P3_empty (X := X))

theorem dense_iff_open_inter_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔
      ∀ U : Set X, IsOpen U → U.Nonempty → (A ∩ U : Set X).Nonempty := by
  classical
  constructor
  · intro hDense U hU_open hU_nonempty
    -- Use the forward implication supplied by `dense_inter_open_nonempty`.
    simpa using
      (dense_inter_open_nonempty (A := A) (U := U)
        hDense hU_open hU_nonempty)
  · intro hProp x
    -- Establish `x ∈ closure A` via the neighbourhood criterion.
    have hx_closure :
        (∀ V : Set X, IsOpen V → x ∈ V → (V ∩ A : Set X).Nonempty) := by
      intro V hV_open hxV
      -- `V` is nonempty because it contains `x`.
      have hV_nonempty : (V : Set X).Nonempty := ⟨x, hxV⟩
      -- Apply the assumed property to obtain a point of `A` in `V`.
      have hInter : (A ∩ V : Set X).Nonempty :=
        hProp V hV_open hV_nonempty
      -- Reorder the intersection to match the required form.
      simpa [Set.inter_comm] using hInter
    exact (mem_closure_iff).2 hx_closure

theorem interior_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interior_closure_interior_closure (A := interior A))

theorem P3_iff_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ (A : Set X) ⊆ interior (closure A) := by
  rfl

theorem closure_interior_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior B) ⊆
      closure (interior (A ∪ B)) := by
  apply closure_mono
  exact Topology.interior_union_subset (A := A) (B := B)

theorem dense_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (A : Set X) → Dense (B : Set X) → Dense (A ∪ B : Set X) := by
  intro hDenseA hDenseB
  -- Density of `A` already suffices to make the union dense.
  have h₁ : Dense (A ∪ B : Set X) :=
    Topology.dense_union_left (A := A) (B := B) hDenseA
  -- Using the density of `B` provides the same conclusion, ensuring both
  -- hypotheses are acknowledged.
  have _h₂ : Dense (A ∪ B : Set X) :=
    Topology.dense_union_right (A := A) (B := B) hDenseB
  exact h₁

theorem P2_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  have hP2B : Topology.P2 (B : Set X) := Topology.P2_of_open hOpenB
  exact Topology.P2_union (A := A) (B := B) hP2A hP2B

theorem P2_of_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (interior A)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x _hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h] using this

theorem closure_interior_closure_eq_closure_interior_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = closure (interior A)) :
    closure (interior (closure (A : Set X))) = closure (interior A) := by
  -- From the given equality we obtain `P1 A`.
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P1_of_closure_eq_closure_interior (A := A) h
  -- `P1` yields an identity relating the two closures we are interested in.
  have hEq :
      closure (A : Set X) = closure (interior (closure (A : Set X))) :=
    Topology.closure_eq_closure_interior_closure_of_P1 (A := A) hP1
  -- Rearrange the equality for convenient rewriting.
  have hEq' :
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
    simpa using hEq.symm
  -- Substitute and finish.
  simpa [hEq', h]

theorem interior_closure_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          simpa using
            (Topology.interior_closure_interior_closure
                (A := interior (closure (A : Set X))))
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure (A := A))

theorem P123_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) (hClosed : IsClosed A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- Since `A` is open, all three properties follow immediately from
  -- `Topology.P123_of_open`.
  simpa using Topology.P123_of_open (A := A) hOpen

theorem P2_closure_of_P1_and_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A)
    (hOpen : IsOpen (closure (interior (closure (A : Set X))))) :
    Topology.P2 (closure (A : Set X)) := by
  -- First, obtain `P1` for `closure A`.
  have hP1Clos : Topology.P1 (closure (A : Set X)) :=
    Topology.P1_closure (A := A) hP1
  -- Apply the existing lemma to turn `P1` into `P2`
  -- using the provided openness assumption.
  have hP2Clos :=
    Topology.P2_of_P1_and_open_closure_interior
      (A := closure (A : Set X)) hP1Clos hOpen
  simpa using hP2Clos

theorem P3_union_of_dense {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) (hDenseB : Dense (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  have hDenseUnion : Dense (A ∪ B : Set X) :=
    Topology.dense_union (A := A) (B := B) hDenseA hDenseB
  exact Topology.P3_of_dense (X := X) (A := A ∪ B) hDenseUnion

theorem interior_inter_subset_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  -- `interior` is monotone with respect to set inclusion on the left factor.
  have hA :
      interior (A ∩ B : Set X) ⊆ interior A := by
    apply interior_mono
    exact Set.inter_subset_left
  -- And similarly for the right factor.
  have hB :
      interior (A ∩ B : Set X) ⊆ interior B := by
    apply interior_mono
    exact Set.inter_subset_right
  -- Combine the two inclusions to obtain the desired membership.
  exact ⟨hA hx, hB hx⟩

theorem nonempty_of_closure_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro hClosInt
  classical
  by_cases hInt : (interior (A : Set X)).Nonempty
  ·
    rcases hInt with ⟨y, hyInt⟩
    exact ⟨y, (interior_subset : interior (A : Set X) ⊆ A) hyInt⟩
  ·
    -- If `interior A` is empty, then its closure is also empty,
    -- contradicting the hypothesis.
    have hIntEq : interior (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hInt
    have hClosEq : closure (interior (A : Set X)) = (∅ : Set X) := by
      simpa [hIntEq, closure_empty]
    rcases hClosInt with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hClosEq] using hx
    exact this.elim

theorem dense_interior_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior (A : Set X))) :
    Dense (interior (closure (A : Set X))) := by
  -- From the density of `interior A`, obtain a closure equality.
  have hClIntA : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (A : Set X))).1 hDense
  -- `interior A` is contained in `interior (closure A)`.
  have hSubInt :
      interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    Topology.interior_subset_interior_closure (A := A)
  -- Taking closures preserves inclusions.
  have hSubClos :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) :=
    closure_mono hSubInt
  -- Combine the two facts to get the desired closure equality.
  have hClIntClos :
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · -- `closure (interior A)` is `univ`, and it sits inside the target closure.
      simpa [hClIntA] using hSubClos
  -- Translate the closure equality back into density.
  exact
    ((Topology.dense_iff_closure_eq_univ
        (A := interior (closure (A : Set X)))).2 hClIntClos)

theorem interior_inter {α : Type*} [TopologicalSpace α] {A B : Set α} :
    interior (A ∩ B) = interior A ∩ interior B := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B : Set α) ⊆ A)) hx
    have hxB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set α) ⊆ B)) hx
    exact And.intro hxA hxB
  · intro x hx
    rcases hx with ⟨hxA, hxB⟩
    -- The set `interior A ∩ interior B` is open and contained in `A ∩ B`.
    have hOpen : IsOpen (interior A ∩ interior B) :=
      (isOpen_interior).inter isOpen_interior
    have hSub : (interior A ∩ interior B : Set α) ⊆ A ∩ B := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1,
             (interior_subset : interior B ⊆ B) hy.2⟩
    have hIncl : (interior A ∩ interior B : Set α) ⊆ interior (A ∩ B) :=
      interior_maximal hSub hOpen
    exact hIncl ⟨hxA, hxB⟩

theorem P1_iff_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ (A : Set X) ⊆ closure (interior A) := by
  rfl

theorem interior_closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    interior (closure (A : Set X)) = Set.univ := by
  -- From the density of `interior A`, obtain that
  -- `interior (closure (interior A)) = univ`.
  have hInt :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) :=
    (Topology.dense_interior_iff_interior_closure_interior_eq_univ (A := A)).1
      hDenseInt
  -- This interior is contained in `interior (closure A)`.
  have hSub :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) :=
    Topology.interior_closure_interior_subset_interior_closure (A := A)
  -- Hence `univ ⊆ interior (closure A)`.
  have hSubUniv :
      (Set.univ : Set X) ⊆ interior (closure (A : Set X)) := by
    simpa [hInt] using hSub
  -- Conclude the desired equality by antisymmetry.
  apply Set.Subset.antisymm
  · intro _ _; trivial
  · exact hSubUniv

theorem closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ, closure_univ]

theorem P2_iff_empty_of_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = (∅ : Set X)) :
    Topology.P2 A ↔ A = ∅ := by
  constructor
  · intro hP2
    -- Unfold the definition of `P2`
    dsimp [Topology.P2] at hP2
    -- `interior A = ∅` implies its closure, and hence the interior of that
    -- closure, are also empty.
    have hClos : closure (interior A) = (∅ : Set X) := by
      ext x
      simp [hInt]
    have hIntClos : interior (closure (interior A)) = (∅ : Set X) := by
      simpa [hClos, interior_empty]
    -- From `hP2`, `A` is contained in this (empty) set.
    have hSub : (A : Set X) ⊆ (∅ : Set X) := by
      intro x hxA
      have : x ∈ interior (closure (interior A)) := hP2 hxA
      simpa [hIntClos] using this
    -- Hence `A` itself is empty.
    have hEq : (A : Set X) = (∅ : Set X) :=
      Set.Subset.antisymm hSub (Set.empty_subset _)
    simpa using hEq
  · intro hA
    -- Rewrite everything using `hA`. The empty set satisfies `P2`.
    simpa [hA] using (Topology.P2_empty (X := X))

theorem P2_closure_interior_closure_iff_open_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure (A : Set X))))
      ↔ IsOpen (closure (interior (closure (A : Set X)))) := by
  have hClosed :
      IsClosed (closure (interior (closure (A : Set X)))) := isClosed_closure
  simpa using
    (Topology.P2_closed_iff_open
        (A := closure (interior (closure (A : Set X)))) hClosed)

theorem P2_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior (closure A)))) := by
  have hOpen : IsOpen (interior (closure (interior (closure A)))) :=
    isOpen_interior
  exact Topology.P2_of_open hOpen

theorem interior_closure_interior_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    interior (closure (interior (A : Set X))) = Set.univ := by
  simpa using
    (dense_interior_iff_interior_closure_interior_eq_univ (A := A)).1
      hDenseInt

theorem isClosed_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    IsClosed (closure (interior (closure (A : Set X)))) := by
  simpa using
    (isClosed_closure :
      IsClosed (closure (interior (closure (A : Set X)))))

theorem P3_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 (closure (A : Set X)) := by
  intro hDenseInt
  -- From the density of `interior A`, deduce the density of `A`.
  have hDenseA : Dense (A : Set X) :=
    Topology.dense_of_dense_interior (A := A) hDenseInt
  -- Apply the existing result that dense sets yield `P3` for their closures.
  exact Topology.P3_closure_of_dense (A := A) hDenseA

theorem closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    closure (A : Set X) = Set.univ := by
  classical
  -- From the density of `interior A`, obtain a closure equality.
  have hInt : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (A : Set X))).1 hDenseInt
  -- `closure (interior A)` is contained in `closure A`.
  have hIncl :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    Topology.closure_interior_subset_closure (A := A)
  -- Hence `univ ⊆ closure A`.
  have hLeft : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    simpa [hInt] using hIncl
  -- The reverse inclusion is trivial.
  have hRight : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro _ _; trivial
  -- Conclude the proof via antisymmetry.
  exact Set.Subset.antisymm hRight hLeft

theorem interior_closure_interior_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  -- `closure (interior A)` is contained in `closure (interior (closure A))`.
  have h : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (A := A)
  -- Taking interiors preserves this inclusion.
  exact interior_mono h

theorem interior_iUnion_of_open {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) (hOpen : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i : Set X) = ⋃ i, A i := by
  -- The union of open sets is open.
  have hUnionOpen : IsOpen (⋃ i, A i : Set X) := isOpen_iUnion hOpen
  -- For an open set, its interior coincides with itself.
  simpa using hUnionOpen.interior_eq

theorem interior_closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B : Set X)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- First inclusion: into `interior (closure A)`.
  have hA :
      interior (closure (A ∩ interior B : Set X)) ⊆
        interior (closure A) := by
    apply interior_mono
    have : closure (A ∩ interior B : Set X) ⊆ closure A := by
      apply closure_mono
      exact Set.inter_subset_left
    exact this
  -- Second inclusion: into `interior (closure B)`.
  have hB :
      interior (closure (A ∩ interior B : Set X)) ⊆
        interior (closure B) := by
    apply interior_mono
    have : closure (A ∩ interior B : Set X) ⊆ closure B := by
      apply closure_mono
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact this
  exact ⟨hA hx, hB hx⟩

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (closure A ∪ closure B) := by
  intro hP1A hP1B
  -- First, upgrade `P1` for `A` and `B` to their closures.
  have hP1ClosA : Topology.P1 (closure A) :=
    Topology.P1_closure (A := A) hP1A
  have hP1ClosB : Topology.P1 (closure B) :=
    Topology.P1_closure (A := B) hP1B
  -- Apply the union lemma to the two closures.
  exact Topology.P1_union hP1ClosA hP1ClosB

theorem P3_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  -- Obtain density of `interior A` from the closure equality.
  have hDenseInt : Dense (interior (A : Set X)) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (A : Set X))).2 h
  -- Convert density into the desired property.
  exact Topology.P3_of_dense_interior (A := A) hDenseInt

theorem interior_closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (∅ : Set X) ↔
      interior (A : Set X) = ∅ := by
  classical
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`,
    -- hence it must also be empty.
    have hSub :
        interior (A : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ interior (closure (interior (A : Set X))) :=
        Topology.interior_subset_interior_closure_interior (A := A) hx
      simpa [h] using this
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro hInt
    -- If `interior A` is empty, so is its closure, and consequently
    -- the interior of that closure is also empty.
    have hClos : closure (interior (A : Set X)) = (∅ : Set X) := by
      simpa [hInt, closure_empty]
    simpa [hClos, interior_empty]

theorem interior_union_eq_self_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa using hOpen.interior_eq

theorem dense_closed_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    (A : Set X) = Set.univ := by
  have hClosure : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  simpa [hClosed.closure_eq] using hClosure

theorem P123_of_dense_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hDense : Dense (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- A closed dense subset of a topological space is the whole space.
  have hEq : (A : Set X) = Set.univ :=
    Topology.dense_closed_eq_univ (A := A) hDense hClosed
  -- All three properties `P1`, `P2`, and `P3` hold for `univ`; rewrite using `hEq`.
  simpa [hEq] using (Topology.P123_univ (X := X))

theorem isOpen_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    IsOpen (closure (A : Set X)) := by
  have hEq : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  simpa [hEq] using (isOpen_univ : IsOpen (Set.univ : Set X))

theorem closure_iInter_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋂ i, A i : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- For each index `i`, show that `x ∈ closure (A i)`.
  have hxi : ∀ i, x ∈ closure (A i) := by
    intro i
    -- The intersection is contained in each component.
    have hSub : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Taking closures preserves inclusions.
    have hClos : closure (⋂ j, A j : Set X) ⊆ closure (A i) :=
      closure_mono hSub
    exact hClos hx
  -- Assemble the pointwise condition into membership in the intersection.
  exact Set.mem_iInter.2 hxi

theorem P3_closure_interior_iff_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_open
      (A := closure (interior (A : Set X))) hClosed)

theorem P1_iff_P2_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    Topology.P1 A ↔ Topology.P2 A := by
  -- From the density of `interior A` we get both `P1` and `P2`.
  have hP1 : Topology.P1 A :=
    Topology.P1_of_dense_interior (A := A) hDenseInt
  have hP2 : Topology.P2 A :=
    Topology.P2_of_dense_interior (A := A) hDenseInt
  constructor
  · intro _; exact hP2
  · intro _; exact hP1

theorem closure_subset_of_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) ⊆ interior (closure (B : Set X))) :
    closure (A : Set X) ⊆ closure (B : Set X) := by
  -- First, upgrade the inclusion to one into `closure B`.
  have h₁ : (A : Set X) ⊆ closure (B : Set X) :=
    Set.Subset.trans h interior_subset
  -- Taking closures preserves inclusions.
  have h₂ :
      closure (A : Set X) ⊆ closure (closure (B : Set X)) :=
    closure_mono h₁
  -- Simplify `closure (closure B)` to `closure B`.
  simpa [closure_closure] using h₂

theorem interior_closure_nonempty_of_nonempty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hInt
  rcases hInt with ⟨x, hxIntA⟩
  have hxIntClos : x ∈ interior (closure (A : Set X)) :=
    (interior_subset_interior_closure (A := A)) hxIntA
  exact ⟨x, hxIntClos⟩

theorem P123_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X)
    (h : ∀ i, Topology.P1 (A i) ∧ Topology.P2 (A i) ∧ Topology.P3 (A i)) :
    Topology.P1 (⋃ i, A i) ∧ Topology.P2 (⋃ i, A i) ∧ Topology.P3 (⋃ i, A i) := by
  have hP1 : ∀ i, Topology.P1 (A i) := fun i => (h i).1
  have hP2 : ∀ i, Topology.P2 (A i) := fun i => (h i).2.1
  have hP3 : ∀ i, Topology.P3 (A i) := fun i => (h i).2.2
  exact
    ⟨Topology.P1_iUnion (A := A) hP1,
      Topology.P2_iUnion (A := A) hP2,
      Topology.P3_iUnion (A := A) hP3⟩

theorem closure_interior_eq_univ_of_P1_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hDense : Dense (A : Set X)) :
    closure (interior (A : Set X)) = (Set.univ : Set X) := by
  classical
  -- Density of `A` gives `closure A = univ`.
  have hClosA : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  -- From `P1`, `closure A ⊆ closure (interior A)`.
  have hIncl : closure (A : Set X) ⊆ closure (interior (A : Set X)) :=
    Topology.closure_subset_closure_interior_of_P1 (A := A) hP1
  -- Hence `univ ⊆ closure (interior A)`.
  have hLeft : (Set.univ : Set X) ⊆ closure (interior (A : Set X)) := by
    simpa [hClosA] using hIncl
  -- Conclude the desired equality.
  apply Set.Subset.antisymm
  · intro _ _; trivial
  · exact hLeft

theorem P2_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  exact Topology.P2_of_open (A := Aᶜ) hOpen

theorem closure_eq_closure_interior_of_open_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (A ∪ B : Set X) = closure (interior (A ∪ B : Set X)) := by
  -- The union of two open sets is open.
  have hOpenUnion : IsOpen (A ∪ B : Set X) := hA.union hB
  -- Apply the existing lemma for open sets to the union.
  simpa using
    (Topology.closure_eq_closure_interior_of_open
      (A := A ∪ B) hOpenUnion)

theorem P123_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P1_of_dense_interior (A := A) hDenseInt
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hDenseInt
  have hP3 : Topology.P3 A := Topology.P3_of_dense_interior (A := A) hDenseInt
  exact ⟨hP1, hP2, hP3⟩

theorem closure_interior_eq_self_of_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  have hClos : closure (A : Set X) = A := hClosed.closure_eq
  calc
    closure (interior (A : Set X)) = closure (A : Set X) := by
      simpa [hInt]
    _ = A := by
      simpa [hClos]

theorem Topology.P3_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  exact Topology.P3_of_open hOpen

theorem P1_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  -- Apply the lemma asserting `P1` for open sets.
  exact Topology.P1_of_open hOpen

theorem dense_interior_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Dense (interior (closure (A : Set X))) := by
  intro hDense
  -- Translate the density of `A` into a closure equality.
  have hEq : closure (interior (closure (A : Set X))) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_interior_closure_eq_univ (A := A)).1 hDense
  -- Reinterpret the equality as density of `interior (closure A)`.
  exact
    (Topology.dense_iff_closure_eq_univ
        (A := interior (closure (A : Set X)))).2 hEq

theorem interior_closure_eq_self_of_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  calc
    interior (closure (A : Set X))
        = interior (A : Set X) :=
          (interior_closure_eq_interior_of_closed (A := A) hClosed)
    _ = A := hOpen.interior_eq

theorem closure_iUnion_interior_subset_closure_interior_iUnion
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋃ i, interior (A i : Set X)) ⊆
      closure (interior (⋃ i, A i : Set X)) := by
  -- First, show that the union of the interiors is contained in the
  -- interior of the union.
  have hSub :
      (⋃ i, interior (A i : Set X)) ⊆ interior (⋃ i, A i : Set X) := by
    intro y hy
    rcases Set.mem_iUnion.1 hy with ⟨i, hyInt⟩
    -- `interior (A i)` sits inside the desired interior by monotonicity.
    have hIntSub :
        interior (A i : Set X) ⊆ interior (⋃ j, A j : Set X) := by
      apply interior_mono
      intro z hz
      exact Set.mem_iUnion.2 ⟨i, hz⟩
    exact hIntSub hyInt
  -- Taking closures preserves inclusions.
  exact closure_mono hSub

theorem interior_closure_eq_interior_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    interior (closure (A : Set X)) =
      interior (closure (interior (closure (A : Set X)))) := by
  -- `P3` gives a closure equality involving `A` and `interior (closure A)`.
  have hClos :
      closure (A : Set X) = closure (interior (closure (A : Set X))) :=
    Topology.closure_eq_closure_interior_closure_of_P3 (A := A) hP3
  -- Applying `interior` to both sides yields the desired result.
  simpa using congrArg (fun s : Set X => interior s) hClos

theorem closure_interior_inter_subset_closure_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) ⊆
      closure (interior A ∩ interior B) := by
  -- First, relate the two interiors directly.
  have hSub :
      interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
    have hxB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    exact ⟨hxA, hxB⟩
  -- Taking closures preserves inclusions.
  exact closure_mono hSub

theorem P3_closure_interior_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P3 (closure (interior (A : Set X))) := by
  -- `closure (interior A)` is closed by definition.
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- For a closed set, `P3` is equivalent to openness.
  have hEquiv :
      Topology.P3 (closure (interior (A : Set X))) ↔
        IsOpen (closure (interior (A : Set X))) :=
    Topology.P3_closed_iff_open
      (A := closure (interior (A : Set X))) hClosed
  exact (hEquiv.mpr hOpen)

theorem closure_iUnion_subset {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) :
    (⋃ i, closure (A i : Set X)) ⊆ closure (⋃ i, A i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hIncl : closure (A i : Set X) ⊆ closure (⋃ j, A j : Set X) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hIncl hxAi

theorem interior_closure_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : (A : Set X).Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  have hIntNonempty : (interior (A : Set X)).Nonempty := by
    by_contra hEmpty
    have hIntEq : interior (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hEmpty
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hIntEq, closure_empty] using hxCl
    exact this
  rcases hIntNonempty with ⟨y, hyIntA⟩
  have hSub : interior (A : Set X) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  have hyIntCl : y ∈ interior (closure A) := hSub hyIntA
  exact ⟨y, hyIntCl⟩

theorem P1_and_P2_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P3 A → (Topology.P1 A ∧ Topology.P2 A) := by
  intro hP3
  have hP1 : Topology.P1 A :=
    Topology.P3_implies_P1_of_closed (A := A) hClosed hP3
  have hP2 : Topology.P2 A :=
    Topology.P3_implies_P2_of_closed (A := A) hClosed hP3
  exact And.intro hP1 hP2

theorem P2_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  -- The hypothesis yields the density of `interior A`.
  have hDenseInt : Dense (interior (A : Set X)) :=
    (Topology.dense_interior_iff_closure_interior_eq_univ (A := A)).2 h
  -- Density of `interior A` implies `P2` for `A`.
  exact Topology.P2_of_dense_interior (A := A) hDenseInt

theorem closure_interior_union_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior (A : Set X) ∪ interior B) = closure (A ∪ B) := by
  have hIntA : interior (A : Set X) = A := hA.interior_eq
  have hIntB : interior (B : Set X) = B := hB.interior_eq
  simpa [hIntA, hIntB]

theorem P3_closure_iff_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure (A : Set X) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_interior_eq
      (A := closure (A : Set X)) hClosed)

theorem P123_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∪ interior B) ∧
      Topology.P2 (interior A ∪ interior B) ∧
      Topology.P3 (interior A ∪ interior B) := by
  -- `interior A` and `interior B` are open sets.
  have hOpenA : IsOpen (interior A) := isOpen_interior
  have hOpenB : IsOpen (interior B) := isOpen_interior
  -- Apply the existing lemma for the union of two open sets.
  simpa using
    (Topology.P123_union_open
      (A := interior A) (B := interior B) hOpenA hOpenB)

theorem interior_closure_inter_left_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆ interior (closure A) := by
  -- `closure` is monotone, hence the closure of an intersection
  -- is contained in the closure of the left factor.
  have h : closure (A ∩ B : Set X) ⊆ closure A := by
    apply closure_mono
    exact Set.inter_subset_left
  -- Taking interiors preserves inclusions.
  exact interior_mono h

theorem isClosed_closure_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (interior (A : Set X)) ∩ closure (interior (B : Set X))) := by
  have hA : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  have hB : IsClosed (closure (interior (B : Set X))) := isClosed_closure
  exact hA.inter hB

theorem closure_union_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure (A ∪ B : Set X) = A ∪ B := by
  have hClosed : IsClosed (A ∪ B : Set X) := hA_closed.union hB_closed
  exact hClosed.closure_eq

theorem isClosed_closure_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (interior (A : Set X)) ∪ closure (interior (B : Set X))) := by
  have hA : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  have hB : IsClosed (closure (interior (B : Set X))) := isClosed_closure
  exact hA.union hB

theorem closure_interior_closure_eq_closure_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- Since `closure A` is open, its interior coincides with itself.
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) :=
    hOpen.interior_eq
  -- Rewrite and simplify using `closure_closure`.
  have : closure (interior (closure (A : Set X))) =
      closure (closure (A : Set X)) := by
    simpa [hInt]
  simpa [closure_closure] using this

theorem interior_closure_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : closure (A : Set X) = closure B) :
    interior (closure (A : Set X)) = interior (closure B) := by
  simpa [h] using
    (rfl : interior (closure (A : Set X)) = interior (closure (A : Set X)))

theorem P1_iff_P2_and_P3_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  constructor
  · intro _hP1
    exact ⟨Topology.P2_of_open hOpen, Topology.P3_of_open hOpen⟩
  · intro h
    exact Topology.P2_implies_P1 h.1

theorem closure_inter_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure (A ∩ B : Set X) = A ∩ B := by
  -- The intersection of two closed sets is itself closed.
  have hClosed : IsClosed (A ∩ B : Set X) := hA_closed.inter hB_closed
  -- The closure of a closed set equals the set itself.
  simpa using hClosed.closure_eq

theorem interior_closure_inter_right_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆ interior (closure B) := by
  -- `closure` is monotone, hence `closure (A ∩ B)` is contained in `closure B`.
  have h : closure (A ∩ B : Set X) ⊆ closure B := by
    apply closure_mono
    exact Set.inter_subset_right
  -- Taking interiors preserves inclusions.
  exact interior_mono h

theorem P123_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  -- Apply the combined property for open sets.
  simpa using Topology.P123_of_open (A := Aᶜ) hOpen

theorem interior_closure_eq_interior_closure_interior_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) :
    interior (closure (A : Set X)) =
      interior (closure (interior (A : Set X))) := by
  have hP2 : Topology.P2 (A : Set X) :=
    Topology.P2_of_open (A := A) hOpen
  exact
    Topology.interior_closure_eq_interior_closure_interior_of_P2
      (A := A) hP2

theorem P123_sUnion {X : Type*} [TopologicalSpace X] (A : Set (Set X))
    (h :
      ∀ B, B ∈ A →
        Topology.P1 (B : Set X) ∧ Topology.P2 (B : Set X) ∧ Topology.P3 (B : Set X)) :
    Topology.P1 (⋃₀ A) ∧ Topology.P2 (⋃₀ A) ∧ Topology.P3 (⋃₀ A) := by
  classical
  -- Extract the individual properties from the combined assumption.
  have hP1 : ∀ B, B ∈ A → Topology.P1 (B : Set X) := fun B hBA => (h B hBA).1
  have hP2 : ∀ B, B ∈ A → Topology.P2 (B : Set X) := fun B hBA => (h B hBA).2.1
  have hP3 : ∀ B, B ∈ A → Topology.P3 (B : Set X) := fun B hBA => (h B hBA).2.2
  -- Apply the existing `sUnion` lemmas component-wise.
  have h₁ : Topology.P1 (⋃₀ A) :=
    Topology.P1_sUnion (A := A) (by
      intro B hBA
      exact hP1 B hBA)
  have h₂ : Topology.P2 (⋃₀ A) :=
    Topology.P2_sUnion (A := A) (by
      intro B hBA
      exact hP2 B hBA)
  have h₃ : Topology.P3 (⋃₀ A) :=
    Topology.P3_sUnion (A := A) (by
      intro B hBA
      exact hP3 B hBA)
  exact ⟨h₁, h₂, h₃⟩



theorem P2_inter_open_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- Unfold the definition of `P2`.
  dsimp [Topology.P2] at hP2A ⊢
  intro x hxAB
  -- Split the hypothesis `x ∈ A ∩ B`.
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P2 A`, obtain that `x` is in the relevant interior.
  have hxIntA : x ∈ interior (closure (interior A)) := hP2A hxA
  -- We shall work with the open neighbourhood `W := interior (closure (interior A)) ∩ B`.
  let W : Set X := interior (closure (interior A)) ∩ B
  have hW_open : IsOpen W :=
    (isOpen_interior.inter hOpenB)
  have hxW : x ∈ W := ⟨hxIntA, hxB⟩
  -- We next show that every point of `W` lies in `closure (interior (A ∩ B))`.
  have hW_subset :
      (W : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hyW
    rcases hyW with ⟨hyIntA, hyB⟩
    -- `y` is in the closure of `interior A`.
    have hyClA : y ∈ closure (interior A) :=
      (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hyIntA
    -- Characterize membership in a closure via neighbourhoods.
    have hMem : y ∈ closure (interior (A ∩ B)) := by
      -- Use the neighbourhood formulation of `closure`.
      refine (mem_closure_iff).2 ?_
      intro U hU_open hyU
      -- Intersect the neighbourhood with `B`, which is open and contains `y`.
      have hV_open : IsOpen (U ∩ B) := hU_open.inter hOpenB
      have hyV : y ∈ U ∩ B := ⟨hyU, hyB⟩
      -- From `hyClA`, the intersection with `interior A` is nonempty.
      have hNonempty :
          ((U ∩ B) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hV_open hyV
      -- Relate `interior (A ∩ B)` to `interior A ∩ B`.
      have hInt_eq :
          interior (A ∩ B : Set X) = interior A ∩ interior B := by
        simpa using interior_inter
      -- Since `B` is open, `interior B = B`.
      have hIntB : interior B = (B : Set X) := hOpenB.interior_eq
      -- The non‐empty intersection yields a point in `U ∩ interior (A ∩ B)`.
      rcases hNonempty with ⟨z, ⟨⟨hzU, hzB⟩, hzIntA⟩⟩
      have hzIntAB : z ∈ interior (A ∩ B) := by
        have : z ∈ interior A ∩ interior B := by
          have hzIntB : z ∈ interior B := by
            simpa [hIntB] using hzB
          exact ⟨hzIntA, hzIntB⟩
        simpa [hInt_eq] using this
      exact ⟨z, ⟨hzU, hzIntAB⟩⟩
    exact hMem
  -- By maximality of the interior, `W` lies inside `interior (closure (interior (A ∩ B)))`.
  have hW_in :
      (W : Set X) ⊆ interior (closure (interior (A ∩ B))) :=
    interior_maximal hW_subset hW_open
  -- Apply the inclusion to the point `x`.
  exact hW_in hxW

theorem closure_interior_union_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior B) ⊆ closure (A ∪ B) := by
  -- First, show the underlying inclusion without the closures.
  have hSub : (interior (A : Set X) ∪ interior B) ⊆ A ∪ B := by
    intro x hx
    cases hx with
    | inl hA =>
        exact Or.inl ((interior_subset : interior (A : Set X) ⊆ A) hA)
    | inr hB =>
        exact Or.inr ((interior_subset : interior (B : Set X) ⊆ B) hB)
  -- The `closure` operator is monotone, so the desired inclusion follows.
  exact closure_mono hSub

theorem P2_inter_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P2_inter_open_right (A := B) (B := A) hP2B hOpenA)

theorem P3_inter_open_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3] at hP3A ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P3` for `A`, obtain that `x` lies in `interior (closure A)`.
  have hxIntA : x ∈ interior (closure A) := hP3A hxA
  -- Consider the open set `W = interior (closure A) ∩ B`.
  let W : Set X := interior (closure A) ∩ B
  have hW_open : IsOpen W :=
    isOpen_interior.inter hOpenB
  have hxW : x ∈ W := by
    exact And.intro hxIntA hxB
  -- We show that `W` is contained in `closure (A ∩ B)`.
  have hW_sub_cl : (W : Set X) ⊆ closure (A ∩ B) := by
    intro y hy
    rcases hy with ⟨hyIntA, hyB⟩
    -- `y ∈ interior (closure A)` implies `y ∈ closure A`.
    have hyClA : y ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hyIntA
    -- Use the neighbourhood characterisation of the closure.
    have : y ∈ closure (A ∩ B) := by
      -- Reformulate `hyClA` via `mem_closure_iff`.
      have hClosureA :=
        (mem_closure_iff).1 hyClA
      -- Show that every open neighbourhood of `y` meets `A ∩ B`.
      have hClosureAB : ∀ U : Set X, IsOpen U → y ∈ U →
          (U ∩ (A ∩ B) : Set X).Nonempty := by
        intro U hU_open hyU
        -- Intersect the neighbourhood with `B`, which is open.
        have hV_open : IsOpen (U ∩ B) := hU_open.inter hOpenB
        have hyV : y ∈ U ∩ B := ⟨hyU, hyB⟩
        -- `U ∩ B` meets `A` since `y ∈ closure A`.
        have hNonempty : ((U ∩ B) ∩ A).Nonempty :=
          hClosureA (U ∩ B) hV_open hyV
        rcases hNonempty with ⟨z, ⟨⟨hzU, hzB⟩, hzA⟩⟩
        -- The point `z` lies in `U ∩ (A ∩ B)`.
        exact ⟨z, ⟨hzU, ⟨hzA, hzB⟩⟩⟩
      -- Translate the neighbourhood property back into membership in the closure.
      exact (mem_closure_iff).2 hClosureAB
    exact this
  -- By maximality of the interior, `W ⊆ interior (closure (A ∩ B))`.
  have hW_sub_int :
      (W : Set X) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal hW_sub_cl hW_open
  -- Conclude by applying the inclusion to `x`.
  exact hW_sub_int hxW

theorem P3_inter_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Swap the factors and reuse the existing right‐hand variant.
  have h := Topology.P3_inter_open_right (A := B) (B := A) hP3B hOpenA
  simpa [Set.inter_comm] using h

theorem closure_union_eq_univ_of_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDense : Dense (B : Set X)) :
    closure (A ∪ B : Set X) = (Set.univ : Set X) := by
  simpa [Set.union_comm] using
    (Topology.closure_union_eq_univ_of_dense_left (A := B) (B := A) hDense)

theorem interior_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ closure (B : Set X) : Set X) ⊆
      interior A ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- Inclusion into `interior A`.
  have hA :
      interior (A ∩ closure (B : Set X) : Set X) ⊆ interior A := by
    apply interior_mono
    exact Set.inter_subset_left
  -- Inclusion into `interior (closure B)`.
  have hB :
      interior (A ∩ closure (B : Set X) : Set X) ⊆
        interior (closure (B : Set X)) := by
    apply interior_mono
    intro y hy
    exact hy.2
  exact ⟨hA hx, hB hx⟩

theorem nonempty_of_interior_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty → (A : Set X).Nonempty := by
  intro hInt
  rcases hInt with ⟨x, hxInt⟩
  exact ⟨x, (interior_subset : interior (A : Set X) ⊆ A) hxInt⟩

theorem closure_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure (A : Set X) := by
  exact closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)

theorem P2_of_P1_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hDense : Dense (A : Set X)) :
    Topology.P2 (A : Set X) := by
  -- First, `closure (interior A) = univ` by the existing lemma.
  have hClos : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    Topology.closure_interior_eq_univ_of_P1_and_dense (A := A) hP1 hDense
  -- Consequently, `interior (closure (interior A)) = univ`.
  have hInt : interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hClos, interior_univ]
  -- Apply the lemma that turns this interior equality into `P2`.
  exact
    Topology.P2_of_interior_closure_interior_eq_univ (A := A) hInt

theorem P1_inter_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) :
    Topology.P1 B → Topology.P1 (A ∩ B) := by
  intro hP1B
  have h := Topology.P1_inter_open (A := B) (B := A) hOpenA hP1B
  simpa [Set.inter_comm] using h



theorem IsOpen.diff {α : Type*} [TopologicalSpace α] {U V : Set α}
    (hU : IsOpen (U : Set α)) (hV : IsClosed (V : Set α)) :
    IsOpen (U \ V : Set α) := by
  have hOpenComplV : IsOpen (Vᶜ : Set α) := by
    simpa using hV.isOpen_compl
  simpa [Set.diff_eq] using hU.inter hOpenComplV

theorem interior_eq_univ_of_closed_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hDense : Dense (A : Set X)) :
    interior (A : Set X) = Set.univ := by
  have hA : (A : Set X) = Set.univ :=
    Topology.dense_closed_eq_univ (A := A) hDense hClosed
  simpa [hA, interior_univ]

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hB_closed : IsClosed B) :
    Topology.P2 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen (Bᶜ : Set X) := hB_closed.isOpen_compl
  -- Apply the intersection lemma with the open complement.
  have hInter : Topology.P2 (A ∩ Bᶜ) :=
    Topology.P2_inter_open_right (A := A) (B := Bᶜ) hP2A hOpenCompl
  simpa [Set.diff_eq] using hInter

theorem interior_closure_inter_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    interior (closure (A ∩ B : Set X)) = interior (A ∩ B : Set X) := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed (A ∩ B : Set X) := hA_closed.inter hB_closed
  -- For a closed set, its closure equals the set itself.
  simpa [hClosed.closure_eq]

theorem interior_diff_eq_diff_closure_of_open
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen (U : Set X)) :
    interior (U \ V : Set X) = U \ closure V := by
  ext x
  constructor
  · intro hx
    -- From `x ∈ interior (U \ V)` we get `x ∈ U \ V`.
    have hxUV : x ∈ U \ V :=
      (interior_subset : interior (U \ V : Set X) ⊆ U \ V) hx
    have hxU : x ∈ U := hxUV.1
    -- Show that `x ∉ closure V`.
    have hxNotCl : x ∉ closure V := by
      by_contra hxCl
      -- `interior (U \ V)` is an open neighbourhood of `x`
      -- contained in `U \ V`, hence disjoint from `V`.
      have hOpenInt : IsOpen (interior (U \ V : Set X)) := isOpen_interior
      have hNonempty :
          ((interior (U \ V : Set X)) ∩ V : Set X).Nonempty :=
        (mem_closure_iff).1 hxCl (interior (U \ V : Set X)) hOpenInt hx
      rcases hNonempty with ⟨y, ⟨hyInt, hyV⟩⟩
      have : y ∈ U \ V :=
        (interior_subset : interior (U \ V : Set X) ⊆ U \ V) hyInt
      exact this.2 hyV
    exact ⟨hxU, hxNotCl⟩
  · rintro ⟨hxU, hxNotCl⟩
    -- Construct an open neighbourhood of `x` contained in `U \ V`.
    have hOpenCompl : IsOpen ((closure V)ᶜ : Set X) :=
      isClosed_closure.isOpen_compl
    have hOpenN : IsOpen (U ∩ (closure V)ᶜ : Set X) :=
      hU.inter hOpenCompl
    have hxN : x ∈ (U ∩ (closure V)ᶜ : Set X) := ⟨hxU, hxNotCl⟩
    have hSub :
        (U ∩ (closure V)ᶜ : Set X) ⊆ U \ V := by
      intro y hy
      rcases hy with ⟨hyU, hyNotCl⟩
      have hyNotV : y ∉ V := by
        intro hyV
        have : y ∈ closure V := subset_closure hyV
        exact hyNotCl this
      exact ⟨hyU, hyNotV⟩
    exact
      (interior_maximal hSub hOpenN) hxN

theorem P1_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    Topology.P1 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen (Bᶜ : Set X) := hB_closed.isOpen_compl
  -- Apply the lemma for the intersection with an open set.
  have hP1_inter :
      Topology.P1 (A ∩ Bᶜ : Set X) :=
    (Topology.P1_inter_open (A := A) (B := Bᶜ) hOpenCompl) hP1A
  simpa [Set.diff_eq] using hP1_inter

theorem interior_union_eq_union_interiors_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = interior A ∪ interior B := by
  have hUnionOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  have hIntUnion : interior (A ∪ B : Set X) = A ∪ B := hUnionOpen.interior_eq
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  simpa [hIntUnion, hIntA, hIntB]



theorem P2_open_diff_closed {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU_open : IsOpen (U : Set X)) (hV_closed : IsClosed (V : Set X)) :
    Topology.P2 (U \ V) := by
  -- `U \ V` is an open set because it is the difference of an open set and a closed set.
  have hOpenDiff : IsOpen (U \ V : Set X) := by
    simpa using (IsOpen.diff (α := X) hU_open hV_closed)
  -- Apply the lemma asserting `P2` for open sets.
  exact Topology.P2_of_open hOpenDiff

theorem interior_diff_subset_diff_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B : Set X) ⊆ A \ closure B := by
  intro x hxInt
  -- From the interior membership we deduce `x ∈ A \ B`.
  have hMem : x ∈ A \ B :=
    (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hxInt
  have hxA : x ∈ A := hMem.1
  -- We now show that `x ∉ closure B`.
  have hxNotCl : x ∉ closure B := by
    intro hxCl
    -- `interior (A \ B)` is an open neighbourhood of `x` disjoint from `B`,
    -- contradicting the definition of `closure`.
    have hNonempty :
        ((interior (A \ B : Set X)) ∩ B : Set X).Nonempty :=
      (mem_closure_iff).1 hxCl (interior (A \ B : Set X))
        isOpen_interior hxInt
    rcases hNonempty with ⟨y, ⟨hyInt, hyB⟩⟩
    have : y ∈ A \ B :=
      (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hyInt
    exact this.2 hyB
  exact ⟨hxA, hxNotCl⟩

theorem P1_of_closed_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hInt : interior (A : Set X) = A) :
    Topology.P1 (A : Set X) := by
  -- Since `A = interior A`, the set `A` is open.
  have hOpen : IsOpen (A : Set X) := by
    simpa [hInt] using (isOpen_interior : IsOpen (interior (A : Set X)))
  -- Apply the existing lemma for open sets.
  exact Topology.P1_of_open (A := A) hOpen

theorem P3_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hDense : Dense (A : Set X)) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- Density gives `closure A = univ`.
  have hCl : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  -- Hence `interior (closure A)` is `univ`.
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hCl, interior_univ]
  -- The goal now follows trivially.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hInt] using this

theorem closure_inter_subset_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure (B : Set X) := by
  exact closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hB_closed : IsClosed B) :
    Topology.P3 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen (Bᶜ : Set X) := hB_closed.isOpen_compl
  -- Apply the intersection lemma with the open complement.
  have hP3_inter :
      Topology.P3 (A ∩ Bᶜ : Set X) :=
    Topology.P3_inter_open_right (A := A) (B := Bᶜ) hP3A hOpenCompl
  simpa [Set.diff_eq] using hP3_inter

theorem P3_open_diff_closed {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU_open : IsOpen (U : Set X)) (hV_closed : IsClosed (V : Set X)) :
    Topology.P3 (U \ V) := by
  -- `U \ V` is open, being the difference of an open set and a closed set.
  have hOpenDiff : IsOpen (U \ V : Set X) := IsOpen.diff hU_open hV_closed
  -- An open set satisfies `P3`.
  exact Topology.P3_of_open hOpenDiff

theorem P2_union_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  have h : Topology.P2 (B ∪ A) :=
    Topology.P2_union_open (A := B) (B := A) hP2B hOpenA
  simpa [Set.union_comm] using h

theorem interior_closure_nonempty_iff_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    (interior (closure (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    exact Topology.nonempty_of_interior_closure_nonempty (A := A) hInt
  · intro hA
    exact Topology.interior_closure_nonempty_of_P3 (A := A) hP3 hA

theorem closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (closure (A : Set X) ∩ interior (B : Set X)) ⊆
      closure (A ∩ B : Set X) := by
  intro x hx
  rcases hx with ⟨hxClA, hxIntB⟩
  -- Prove `x ∈ closure (A ∩ B)` using the neighbourhood criterion.
  have : x ∈ closure (A ∩ B : Set X) := by
    refine (mem_closure_iff).2 ?_
    intro U hU_open hxU
    -- Consider the open neighbourhood `U ∩ interior B` of `x`.
    have hV_open : IsOpen (U ∩ interior (B : Set X)) :=
      hU_open.inter isOpen_interior
    have hxV : x ∈ U ∩ interior (B : Set X) := ⟨hxU, hxIntB⟩
    -- Since `x ∈ closure A`, this neighbourhood intersects `A`.
    have hNonempty : ((U ∩ interior (B : Set X)) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClA (U ∩ interior (B : Set X)) hV_open hxV
    rcases hNonempty with ⟨y, ⟨⟨hyU, hyIntB⟩, hyA⟩⟩
    -- The point `y` lies in `U ∩ (A ∩ B)`.
    have hy : y ∈ U ∩ (A ∩ B) := by
      have hyB : y ∈ (B : Set X) := interior_subset hyIntB
      exact ⟨hyU, ⟨hyA, hyB⟩⟩
    exact ⟨y, hy⟩
  exact this

theorem P2_iff_P3_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 hP2
  · intro _hP3
    exact Topology.P2_of_dense_interior (A := A) hDenseInt

theorem interior_diff_eq_self_of_open_closed
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU_open : IsOpen (U : Set X)) (hV_closed : IsClosed (V : Set X)) :
    interior (U \ V : Set X) = U \ V := by
  have h :=
    interior_diff_eq_diff_closure_of_open
      (X := X) (U := U) (V := V) hU_open
  simpa [hV_closed.closure_eq] using h

theorem P1_open_diff_closed {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU_open : IsOpen (U : Set X)) (hV_closed : IsClosed (V : Set X)) :
    Topology.P1 (U \ V) := by
  -- `U \ V` is open as the difference of an open set and a closed set.
  have hOpenDiff : IsOpen (U \ V : Set X) := IsOpen.diff hU_open hV_closed
  -- An open set satisfies property `P1`.
  exact Topology.P1_of_open hOpenDiff

theorem P123_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) →
      Topology.P1 (closure (A : Set X)) ∧
        Topology.P2 (closure (A : Set X)) ∧
        Topology.P3 (closure (A : Set X)) := by
  intro hDense
  have hP1 := Topology.P1_closure_of_dense (A := A) hDense
  have hP2 := Topology.P2_closure_of_dense (A := A) hDense
  have hP3 := Topology.P3_closure_of_dense (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩

theorem dense_compl_iff_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense ((Aᶜ) : Set X) ↔ interior (A : Set X) = ∅ := by
  classical
  -- `→`  Direction: density of the complement forces `interior A = ∅`.
  have h₁ : Dense (Aᶜ : Set X) → interior (A : Set X) = ∅ := by
    intro hDense
    by_contra hIntNe
    -- From `hIntNe`, obtain a point in `interior A`.
    have hIntNonempty : (interior (A : Set X)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hIntNe
    -- Use the open–intersection characterization of density.
    have hProp :=
      (Topology.dense_iff_open_inter_nonempty
          (A := (Aᶜ : Set X))).1 hDense
    have hInter :=
      hProp (interior (A : Set X)) isOpen_interior hIntNonempty
    rcases hInter with ⟨x, ⟨hxCompl, hxInt⟩⟩
    -- But `interior A ⊆ A`, contradicting `x ∈ Aᶜ`.
    have hxA : (x : X) ∈ A := interior_subset hxInt
    exact (hxCompl hxA).elim
  -- `←`  Direction: empty interior implies density of the complement.
  have h₂ : interior (A : Set X) = ∅ → Dense (Aᶜ : Set X) := by
    intro hIntEmpty
    -- Establish the open–intersection property required for density.
    have hProp :
        ∀ U : Set X, IsOpen U → U.Nonempty →
          ((Aᶜ : Set X) ∩ U).Nonempty := by
      intro U hU_open hU_nonempty
      by_contra hEmpty
      -- If the intersection is empty, `U` is contained in `A`.
      have hSub : (U : Set X) ⊆ A := by
        intro x hxU
        by_contra hxNotA
        have hxCompl : x ∈ (Aᶜ : Set X) := hxNotA
        have hNE : ((Aᶜ : Set X) ∩ U).Nonempty := ⟨x, ⟨hxCompl, hxU⟩⟩
        exact hEmpty hNE
      -- Since `U` is open and `U ⊆ A`, we get `U ⊆ interior A = ∅`.
      have hSubInt : (U : Set X) ⊆ interior A :=
        interior_maximal hSub hU_open
      rcases hU_nonempty with ⟨x, hxU⟩
      have : (x : X) ∈ interior A := hSubInt hxU
      simpa [hIntEmpty] using this
    -- Apply the characterization to conclude density.
    exact
      (Topology.dense_iff_open_inter_nonempty (A := (Aᶜ : Set X))).2 hProp
  exact ⟨h₁, h₂⟩

theorem P2_union_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP2A : Topology.P2 A) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  -- Translate `P2` for the closed sets `A` and `B` into openness.
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_open (A := A) hA_closed).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_open (A := B) hB_closed).1 hP2B
  -- The union of two open sets is open.
  have hOpenUnion : IsOpen (A ∪ B) := hOpenA.union hOpenB
  -- Apply `P2` for open sets.
  exact Topology.P2_of_open hOpenUnion

theorem closure_interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen (B : Set X)) :
    closure (interior (A ∩ B : Set X)) = closure (interior A ∩ B) := by
  -- Use the general formula for the interior of an intersection.
  have hInt : interior (A ∩ B : Set X) = interior A ∩ interior B :=
    interior_inter
  -- Since `B` is open, its interior coincides with itself.
  have hIntB : interior (B : Set X) = B := hB.interior_eq
  -- Rewrite the interior of the intersection accordingly.
  have hEq : interior (A ∩ B : Set X) = interior A ∩ B := by
    simpa [hIntB] using hInt
  -- Take closures on both sides of the equality.
  simpa [hEq]

theorem P123_open_diff_closed {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU_open : IsOpen (U : Set X)) (hV_closed : IsClosed (V : Set X)) :
    Topology.P1 (U \ V) ∧ Topology.P2 (U \ V) ∧ Topology.P3 (U \ V) := by
  -- The difference of an open set and a closed set is open.
  have hOpenDiff : IsOpen (U \ V : Set X) := IsOpen.diff hU_open hV_closed
  -- Apply the combined `P123` result for open sets.
  exact Topology.P123_of_open hOpenDiff

theorem closure_inter_closure_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∩ closure B) = closure A ∩ closure B := by
  have hClosed :
      IsClosed (closure (A : Set X) ∩ closure B) :=
    (isClosed_closure.inter isClosed_closure)
  simpa using hClosed.closure_eq

theorem interior_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    interior ((Aᶜ) : Set X) = Aᶜ := by
  simpa using hA_closed.isOpen_compl.interior_eq

theorem interior_closure_union_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure B)) :
    interior (closure (A ∪ B : Set X)) = closure (A : Set X) ∪ closure B := by
  -- Rewrite the closure of the union using `closure_union`.
  have hClos : closure (A ∪ B : Set X) = closure (A : Set X) ∪ closure B := by
    simpa [closure_union]
  -- The right‐hand side is an open set (union of two open sets).
  have hOpen : IsOpen (closure (A : Set X) ∪ closure B) := hA.union hB
  -- For an open set, its interior coincides with itself.
  have hInt :
      interior (closure (A : Set X) ∪ closure B) =
        closure (A : Set X) ∪ closure B := hOpen.interior_eq
  -- Combine the two equalities.
  simpa [hClos] using hInt

theorem closure_iInter_eq_iInter_of_closed {ι : Sort _} {X : Type _}
    [TopologicalSpace X] (A : ι → Set X) (hClosed : ∀ i, IsClosed (A i)) :
    closure (⋂ i, A i : Set X) = ⋂ i, A i := by
  have h : IsClosed (⋂ i, A i : Set X) := isClosed_iInter (fun i ↦ hClosed i)
  simpa using h.closure_eq

theorem P1_union_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP1B : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  have h := Topology.P1_union_open (A := B) (B := A) hP1B hOpenA
  simpa [Set.union_comm] using h

theorem closure_interior_inter_open_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (interior (A ∩ B : Set X)) = closure (A ∩ interior B) := by
  -- Use the general formula for the interior of an intersection.
  have hInt : interior (A ∩ B : Set X) = interior A ∩ interior B :=
    interior_inter
  -- Since `A` is open, its interior is itself.
  have hIntA : interior (A : Set X) = A := hA.interior_eq
  -- Rewrite the interior of the intersection accordingly.
  have hEq : interior (A ∩ B : Set X) = A ∩ interior B := by
    simpa [hIntA] using hInt
  -- Take closures of both sides of the equality.
  simpa [hEq]

theorem P3_union_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∪ B) := by
  -- The open set `A` itself satisfies `P3`.
  have hP3A : Topology.P3 (A : Set X) := Topology.P3_of_open hOpenA
  -- Combine the two `P3` properties.
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B



theorem clopen_of_closed_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 A) :
    IsClopen (A : Set X) := by
  refine ⟨hClosed, ?_⟩
  exact isOpen_of_closed_P2 (A := A) hClosed hP2

theorem clopen_of_closed_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 A) :
    IsClopen (A : Set X) := by
  -- From `P3` and the closedness of `A`, we deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_closed_iff_open (A := A) hClosed).1 hP3
  -- Combine the closedness and openness to obtain that `A` is clopen.
  exact ⟨hClosed, hOpen⟩

theorem interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  -- `interior (closure A)` is contained in `closure A`.
  have hIntSub : interior (closure (A : Set X)) ⊆ closure A :=
    interior_subset
  -- `closure A` is contained in `closure (interior A)` by `P1`.
  have hClosSub : closure (A : Set X) ⊆ closure (interior A) :=
    Topology.closure_subset_closure_interior_of_P1 (A := A) hP1
  -- Combine the two inclusions.
  exact Set.Subset.trans hIntSub hClosSub

theorem interior_inter_closure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (interior (A : Set X) ∩ closure (B : Set X)) ⊆
      closure (A ∩ B : Set X) := by
  simpa [Set.inter_comm] using
    (closure_inter_interior_subset_closure_inter (A := B) (B := A))

theorem interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen (U : Set X)) :
    interior (U ∩ A : Set X) = U ∩ interior A := by
  simpa [hU.interior_eq] using
    (interior_inter (A := U) (B := A))

theorem interior_closure_eq_self_of_closed_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 A) :
    interior (closure (A : Set X)) = A := by
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_closed_iff_open (A := A) hClosed).1 hP3
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  have hClos : closure (A : Set X) = A := hClosed.closure_eq
  calc
    interior (closure (A : Set X)) = interior (A : Set X) := by
      simpa [hClos]
    _ = A := hInt

theorem interior_diff_eq_diff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB_closed : IsClosed (B : Set X)) :
    interior (A \ B : Set X) = interior A \ B := by
  ext x
  constructor
  · intro hx
    -- `x` belongs to `interior A` because `A \ B ⊆ A`.
    have hxIntA : x ∈ interior A :=
      (interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)) hx
    -- `x` is not in `B` since it lies in `A \ B`.
    have hxNotB : x ∉ B := by
      have : x ∈ (A \ B : Set X) :=
        (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hx
      exact this.2
    exact ⟨hxIntA, hxNotB⟩
  · rintro ⟨hxIntA, hxNotB⟩
    -- The set `interior A \ B` is an open neighbourhood of `x`
    -- contained in `A \ B`, so `x` lies in the interior of `A \ B`.
    have hOpen : IsOpen ((interior A) \ B : Set X) :=
      IsOpen.diff isOpen_interior hB_closed
    have hxIn : x ∈ (interior A) \ B := ⟨hxIntA, hxNotB⟩
    -- `interior A \ B` is contained in `A \ B`.
    have hSub : ((interior A) \ B : Set X) ⊆ A \ B := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1, hy.2⟩
    exact (interior_maximal hSub hOpen) hxIn

theorem P2_inter_closed_of_P3 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP3A : Topology.P3 A) (hP3B : Topology.P3 B) :
    Topology.P2 (A ∩ B) := by
  -- Translate `P3` for the closed sets `A` and `B` into their openness.
  have hOpenA : IsOpen A :=
    (Topology.P3_closed_iff_open hA_closed).1 hP3A
  have hOpenB : IsOpen B :=
    (Topology.P3_closed_iff_open hB_closed).1 hP3B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- Apply `P2` for open sets.
  exact Topology.P2_of_open hOpenInter

theorem P123_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClopen : IsClopen (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  rcases hClopen with ⟨hClosed, hOpen⟩
  simpa using Topology.P123_of_clopen (A := A) hOpen hClosed

theorem compl_empty {α : Type*} :
    ((∅ : Set α)ᶜ) = (Set.univ : Set α) := by
  ext x
  simp

theorem interior_closure_inter_closure_left_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ closure (B : Set X) : Set X)) ⊆
      interior (closure (A : Set X)) := by
  -- `closure` is monotone with respect to set inclusion.
  have h :
      closure (A ∩ closure (B : Set X) : Set X) ⊆ closure (A : Set X) := by
    apply closure_mono
    intro x hx
    exact hx.1
  -- Taking interiors preserves inclusions.
  exact interior_mono h

theorem interior_inter_subset_interiors_alt
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  exact
    ⟨(interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx,
     (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx⟩

theorem closure_union_closure_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∪ closure (B : Set X)) = closure (A ∪ B) := by
  calc
    closure (A ∪ closure (B : Set X))
        = closure A ∪ closure (closure (B : Set X)) := by
          simpa [closure_union]
    _ = closure A ∪ closure (B : Set X) := by
          simpa [closure_closure]
    _ = closure (A ∪ B) := by
          simpa [closure_union]

theorem closure_union_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∪ B) = closure (A ∪ B) := by
  calc
    closure (closure (A : Set X) ∪ B)
        = closure (closure (A : Set X)) ∪ closure B := by
          simpa [closure_union]
    _ = closure (A : Set X) ∪ closure B := by
          simpa [closure_closure]
    _ = closure (A ∪ B : Set X) := by
          simpa [closure_union]

theorem interior_closure_union_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) (hDenseB : Dense (B : Set X)) :
    interior (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
  -- `Dense` sets have closures equal to `univ`.
  have hClosA : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDenseA
  have hClosB : closure (B : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := B)).1 hDenseB
  -- Compute the closure of the union.
  have hClosUnion : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    calc
      closure (A ∪ B : Set X)
          = closure (A : Set X) ∪ closure (B : Set X) := by
              simpa [closure_union]
      _ = (Set.univ : Set X) ∪ (Set.univ : Set X) := by
              simpa [hClosA, hClosB]
      _ = (Set.univ : Set X) := by
              simp
  -- The interior of `univ` is `univ`.
  simpa [hClosUnion, interior_univ]

theorem interior_isClosed_iff_closure_eq_self
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (interior (A : Set X)) ↔ closure (interior (A : Set X)) = interior A := by
  constructor
  · intro hClosed
    simpa using hClosed.closure_eq
  · intro hEq
    have hClosed' : IsClosed (closure (interior (A : Set X))) := isClosed_closure
    simpa [hEq] using hClosed'

theorem closure_interior_eq_univ_of_P2_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hDense : Dense (A : Set X)) :
    closure (interior (A : Set X)) = (Set.univ : Set X) := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.closure_interior_eq_univ_of_P1_and_dense (A := A) hP1 hDense

theorem closure_interior_union_eq_union_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ B) =
      closure (interior (A : Set X)) ∪ closure B := by
  simpa [closure_union]

theorem dense_of_dense_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (closure (A : Set X))) → Dense (A : Set X) := by
  intro hDenseIntClos
  -- Translate density into a closure equality.
  have hEq :
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (closure (A : Set X)))).1 hDenseIntClos
  -- Apply the existing lemma that derives density of `A` from this equality.
  exact
    Topology.dense_of_closure_interior_closure_eq_univ
      (A := A) hEq

theorem closure_interior_inter_subset_closures_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ B) ⊆ closure A ∩ closure B := by
  have h :
      closure (B ∩ interior (A : Set X)) ⊆ closure B ∩ closure A :=
    closure_inter_interior_subset_closures (A := B) (B := A)
  simpa [Set.inter_comm] using h

theorem P2_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (interior A ∪ interior B) := by
  simpa using (Topology.P123_interior_union (A := A) (B := B)).2.1

theorem closure_inter_closure_subset_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure (B : Set X) : Set X) ⊆ closure (A : Set X) := by
  -- The set `A ∩ closure B` is obviously contained in `A`.
  have hSub : (A ∩ closure (B : Set X) : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions, yielding the desired result.
  exact closure_mono hSub

theorem interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = A ∪ B := by
  -- The union of two open sets is open.
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  -- For an open set, its interior coincides with itself.
  simpa using hOpen.interior_eq

theorem isOpen_closure_of_P1_and_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpen : IsOpen (closure (interior A))) :
    IsOpen (closure A) := by
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [hEq] using hOpen

theorem closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  have h₁ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure
        (A := interior A))
  have h₂ :
      closure (interior (closure (interior A))) =
        closure (interior A) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (A := A))
  simpa [h₁, h₂]

theorem P3_closure_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P3 (closure (A : Set X)) :=
  ((Topology.P3_closure_iff_open_closure (A := A)).mpr hOpen)

theorem closure_interior_inter_interior_subset_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hA :
      closure (interior (A : Set X) ∩ interior B) ⊆ closure (interior A) := by
    apply closure_mono
    exact Set.inter_subset_left
  have hB :
      closure (interior (A : Set X) ∩ interior B) ⊆ closure (interior B) := by
    apply closure_mono
    exact Set.inter_subset_right
  exact ⟨hA hx, hB hx⟩

theorem closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) \ closure B ⊆ closure (A \ B : Set X) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotClB⟩
  -- We will verify the neighbourhood criterion for `closure (A \ B)`.
  have h :
      ∀ U : Set X, IsOpen U → x ∈ U →
        ((U ∩ (A \ B)) : Set X).Nonempty := by
    intro U hU hxU
    -- Shrink the neighbourhood so that it is disjoint from `B`.
    have hOpenCompl : IsOpen ((closure B)ᶜ : Set X) :=
      isClosed_closure.isOpen_compl
    have hVopen : IsOpen (U ∩ (closure B)ᶜ) := hU.inter hOpenCompl
    have hxV : x ∈ U ∩ (closure B)ᶜ := by
      exact And.intro hxU hxNotClB
    -- Since `x ∈ closure A`, this neighbourhood meets `A`.
    have hNonempty :
        ((U ∩ (closure B)ᶜ) ∩ A : Set X).Nonempty :=
      (mem_closure_iff).1 hxClA (U ∩ (closure B)ᶜ) hVopen hxV
    rcases hNonempty with ⟨y, ⟨⟨hyU, hyNotClB⟩, hyA⟩⟩
    -- Points outside `closure B` are certainly outside `B`.
    have hyNotB : (y : X) ∉ B := by
      intro hyB
      have : (y : X) ∈ closure B := subset_closure hyB
      exact hyNotClB this
    -- Hence `y ∈ U ∩ (A \ B)`.
    exact ⟨y, ⟨hyU, ⟨hyA, hyNotB⟩⟩⟩
  -- Conclude that `x ∈ closure (A \ B)` by the neighbourhood criterion.
  exact (mem_closure_iff).2 h

theorem P2_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClopen : IsClopen (A : Set X)) :
    Topology.P2 A := by
  exact (Topology.P123_of_isClopen (A := A) hClopen).2.1

theorem interior_eq_empty_iff_closure_complement_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = ∅ ↔ closure (Aᶜ : Set X) = (Set.univ : Set X) := by
  classical
  have h₁ :=
    (Topology.dense_compl_iff_interior_eq_empty (A := A)).symm
  have h₂ :=
    (Topology.dense_iff_closure_eq_univ (A := (Aᶜ : Set X)))
  simpa using h₁.trans h₂

theorem closure_union_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) (hDenseB : Dense (B : Set X)) :
    closure (A ∪ B : Set X) = (Set.univ : Set X) := by
  -- Use the existing lemma for the left factor.
  have _ :=
    Topology.closure_union_eq_univ_of_dense_right (A := A) (B := B) hDenseB
  exact
    Topology.closure_union_eq_univ_of_dense_left (A := A) (B := B) hDenseA

theorem P2_iff_P3_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClopen : IsClopen (A : Set X)) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- A clopen set is, in particular, open.
  have hOpen : IsOpen (A : Set X) := hClopen.2
  -- For open sets, `P2` and `P3` are equivalent.
  simpa using Topology.P2_iff_P3_of_open (A := A) hOpen

theorem P3_compl_of_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = ∅) :
    Topology.P3 (Aᶜ) := by
  -- From the emptiness of `interior A`, deduce that `Aᶜ` is dense.
  have hDense : Dense ((Aᶜ) : Set X) :=
    (Topology.dense_compl_iff_interior_eq_empty (A := A)).2 hInt
  -- Density implies property `P3`.
  exact Topology.P3_of_dense (A := Aᶜ) hDense

theorem P1_iff_P2_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClopen : IsClopen (A : Set X)) :
    Topology.P1 A ↔ Topology.P2 A := by
  have hOpen : IsOpen (A : Set X) := hClopen.2
  simpa using Topology.P1_iff_P2_of_open (A := A) hOpen

theorem P2_closed_iff_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ IsClopen (A : Set X) := by
  -- For a closed set, `P2` is equivalent to openness.
  have hP2_open : Topology.P2 A ↔ IsOpen (A : Set X) :=
    Topology.P2_closed_iff_open (A := A) hA_closed
  -- Openness is equivalent to being clopen when closedness is already given.
  have hOpen_clopen : IsOpen (A : Set X) ↔ IsClopen (A : Set X) := by
    constructor
    · intro hOpen
      exact ⟨hA_closed, hOpen⟩
    · intro hClopen
      exact hClopen.2
  exact hP2_open.trans hOpen_clopen