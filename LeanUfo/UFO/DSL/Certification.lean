import LeanUfo.UFO.Core.Section4

/-!
# Decidable certification support for finite UFO models

This module is deliberately small and conservative: it does **not** alter the
semantic UFO kernel.  The kernel still consists of the Prop-valued signatures
and axiom typeclasses in `LeanUfo/UFO/Core`.

The DSL introduced in this directory compiles user-facing model syntax into a
finite semantic signature.  Once the domain and world type are finite, every
axiom in the current development is a decidable proposition.  Lean can decide
the individual axiom propositions, but it does not automatically know how to
decide the *typeclass packages* such as `UFOAxioms4`.  The instances below are
the missing bridge: each package is decidable exactly when its fields are.

These instances are support infrastructure for proof-producing finite
certification.  The current `ufo_model ... certify` command emits explicit
record-field proofs for `UFOAxioms4`.  The bridge instances here make the axiom
packages available to decidability-based experiments and future checker APIs.
This is checker completeness relative to the finite model representation, not a
proof-theoretic completeness theorem for UFO itself.
-/

namespace LeanUfo.UFO.DSL

/-!
## Finite quantifier reflection

The generated certificates unfold a DSL model into concrete `Fin n` domains.
The two lemmas below teach `simp` how to enumerate those domains recursively:
universal quantification over `Fin (n + 1)` becomes the last element plus the
smaller `Fin n` prefix, and existential quantification becomes the corresponding
disjunction.  This is finite-model checker automation; it is not a logical
completeness result for UFO.
-/

theorem forallFinSucc {n : Nat} {P : Fin (n + 1) → Prop} :
    (∀ i, P i) ↔ (∀ i : Fin n, P i.castSucc) ∧ P (Fin.last n) :=
  ⟨fun h => ⟨fun i => h i.castSucc, h (Fin.last n)⟩,
   fun h i => Fin.lastCases h.2 h.1 i⟩

theorem existsFinSucc {n : Nat} {P : Fin (n + 1) → Prop} :
    (∃ i, P i) ↔ (∃ i : Fin n, P i.castSucc) ∨ P (Fin.last n) :=
  ⟨fun h =>
    Exists.elim h fun i hi =>
      Fin.lastCases
        (motive := fun i => P i → (∃ i : Fin n, P i.castSucc) ∨ P (Fin.last n))
        (fun hi => Or.inr hi)
        (fun j hj => Or.inl ⟨j, hj⟩)
        i hi,
   fun h =>
    Or.elim h
      (fun hPrefix => Exists.elim hPrefix fun i hi => ⟨i.castSucc, hi⟩)
      (fun hLast => ⟨Fin.last n, hLast⟩)⟩

/-!
The following instances are intentionally phrased as equivalences with nested
conjunctions.  That keeps the trusted bridge transparent: a value of an axiom
package is just a record containing one proof per axiom, and conversely the
record fields give back those proofs.
-/

instance decidableUFOAxioms3_1 (Sig : UFOSignature3_1)
    [Decidable (ax_a1 Sig)] [Decidable (ax_a2 Sig)] [Decidable (ax_a3 Sig)]
    [Decidable (ax_a4 Sig)] [Decidable (ax_a5 Sig)] [Decidable (ax_a6 Sig)]
    [Decidable (ax_a7 Sig)] [Decidable (ax_a8 Sig)] [Decidable (ax_a9 Sig)]
    [Decidable (ax_a10 Sig)] [Decidable (ax_a11 Sig)] [Decidable (ax_a12 Sig)]
    [Decidable (ax_a13 Sig)] [Decidable (ax_a14 Sig)] [Decidable (ax_a15 Sig)]
    [Decidable (ax_a16 Sig)] [Decidable (ax_a17 Sig)] :
    Decidable (UFOAxioms3_1 Sig) :=
  decidable_of_iff
    (ax_a1 Sig ∧ ax_a2 Sig ∧ ax_a3 Sig ∧ ax_a4 Sig ∧ ax_a5 Sig ∧
     ax_a6 Sig ∧ ax_a7 Sig ∧ ax_a8 Sig ∧ ax_a9 Sig ∧ ax_a10 Sig ∧
     ax_a11 Sig ∧ ax_a12 Sig ∧ ax_a13 Sig ∧ ax_a14 Sig ∧ ax_a15 Sig ∧
     ax_a16 Sig ∧ ax_a17 Sig)
    ⟨by
      intro h
      rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
      exact
        { ax1 := h1
          ax2 := h2
          ax3 := h3
          ax4 := h4
          ax5 := h5
          ax6 := h6
          ax7 := h7
          ax8 := h8
          ax9 := h9
          ax10 := h10
          ax11 := h11
          ax12 := h12
          ax13 := h13
          ax14 := h14
          ax15 := h15
          ax16 := h16
          ax17 := h17 },
     by
      intro h
      exact ⟨h.ax1, h.ax2, h.ax3, h.ax4, h.ax5, h.ax6, h.ax7, h.ax8, h.ax9,
        h.ax10, h.ax11, h.ax12, h.ax13, h.ax14, h.ax15, h.ax16, h.ax17⟩⟩

instance decidableUFOAxioms3_2 (Sig : UFOSignature3_2)
    [Decidable (UFOAxioms3_1 Sig.toUFOSignature3_1)]
    [Decidable (ax_a18 Sig)] [Decidable (ax_a19 Sig)] [Decidable (ax_a20 Sig)]
    [Decidable (ax_a21 Sig)] [Decidable (ax_a22 Sig)] [Decidable (ax_a23 Sig)]
    [Decidable (ax_a24 Sig)] [Decidable (ax_a25 Sig)] [Decidable (ax_a26 Sig)]
    [Decidable (ax_a27 Sig)] [Decidable (ax_a28 Sig)] [Decidable (ax_a29 Sig)]
    [Decidable (ax_a30 Sig)] [Decidable (ax_a31 Sig)] [Decidable (ax_a32 Sig)]
    [Decidable (ax_a33 Sig)]
    [Decidable (ax_instEndurant_of_EndurantType (Sig := Sig))]
    [Decidable (ax_sub_of_kind_is_sortal (Sig := Sig))]
    [Decidable (ax_nonSortal_upward (Sig := Sig))]
    [Decidable (ax_kindStable Sig)] :
    Decidable (UFOAxioms3_2 Sig) :=
  decidable_of_iff
    (UFOAxioms3_1 Sig.toUFOSignature3_1 ∧
     ax_a18 Sig ∧ ax_a19 Sig ∧ ax_a20 Sig ∧ ax_a21 Sig ∧ ax_a22 Sig ∧
     ax_a23 Sig ∧ ax_a24 Sig ∧ ax_a25 Sig ∧ ax_a26 Sig ∧ ax_a27 Sig ∧
     ax_a28 Sig ∧ ax_a29 Sig ∧ ax_a30 Sig ∧ ax_a31 Sig ∧ ax_a32 Sig ∧
     ax_a33 Sig ∧ ax_instEndurant_of_EndurantType (Sig := Sig) ∧
     ax_sub_of_kind_is_sortal (Sig := Sig) ∧ ax_nonSortal_upward (Sig := Sig) ∧
     ax_kindStable Sig)
    ⟨by
      intro h
      rcases h with ⟨h1, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
        h28, h29, h30, h31, h32, h33, hInst, hSub, hNon, hStable⟩
      exact
        { toUFOAxioms3_1 := h1
          ax18 := h18
          ax19 := h19
          ax20 := h20
          ax21 := h21
          ax22 := h22
          ax23 := h23
          ax24 := h24
          ax25 := h25
          ax26 := h26
          ax27 := h27
          ax28 := h28
          ax29 := h29
          ax30 := h30
          ax31 := h31
          ax32 := h32
          ax33 := h33
          ax_instEndurant := hInst
          ax_sub_kind_sortal := hSub
          ax_nonSortal_up := hNon
          ax_kindStable := hStable },
     by
      intro h
      exact ⟨h.toUFOAxioms3_1, h.ax18, h.ax19, h.ax20, h.ax21, h.ax22, h.ax23,
        h.ax24, h.ax25, h.ax26, h.ax27, h.ax28, h.ax29, h.ax30, h.ax31, h.ax32,
        h.ax33, h.ax_instEndurant, h.ax_sub_kind_sortal, h.ax_nonSortal_up,
        h.ax_kindStable⟩⟩

instance decidableUFOAxioms3_3 (Sig : UFOSignature3_3)
    [Decidable (UFOAxioms3_2 Sig.toUFOSignature3_2)]
    [Decidable (ax_a34 Sig)] [Decidable (ax_a35 Sig)] [Decidable (ax_a36 Sig)]
    [Decidable (ax_a37 Sig)] [Decidable (ax_a38 Sig)] [Decidable (ax_a39 Sig)]
    [Decidable (ax_a40 Sig)] [Decidable (ax_a41 Sig)] [Decidable (ax_a42 Sig)]
    [Decidable (ax_a43 Sig)] :
    Decidable (UFOAxioms3_3 Sig) :=
  decidable_of_iff
    (UFOAxioms3_2 Sig.toUFOSignature3_2 ∧ ax_a34 Sig ∧ ax_a35 Sig ∧
     ax_a36 Sig ∧ ax_a37 Sig ∧ ax_a38 Sig ∧ ax_a39 Sig ∧ ax_a40 Sig ∧
     ax_a41 Sig ∧ ax_a42 Sig ∧ ax_a43 Sig)
    ⟨by
      intro h
      rcases h with ⟨h2, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43⟩
      exact
        { toUFOAxioms3_2 := h2
          ax34 := h34
          ax35 := h35
          ax36 := h36
          ax37 := h37
          ax38 := h38
          ax39 := h39
          ax40 := h40
          ax41 := h41
          ax42 := h42
          ax43 := h43 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_2, h.ax34, h.ax35, h.ax36, h.ax37, h.ax38, h.ax39,
        h.ax40, h.ax41, h.ax42, h.ax43⟩⟩

instance decidableUFOAxioms3_4 (Sig : UFOSignature3_4)
    [Decidable (UFOAxioms3_3 Sig.toUFOSignature3_3)]
    [Decidable (ax_a44 Sig)] [Decidable (ax_a45 Sig)] [Decidable (ax_a46 Sig)] :
    Decidable (UFOAxioms3_4 Sig) :=
  decidable_of_iff
    (UFOAxioms3_3 Sig.toUFOSignature3_3 ∧ ax_a44 Sig ∧ ax_a45 Sig ∧ ax_a46 Sig)
    ⟨by
      intro h
      exact
        { toUFOAxioms3_3 := h.1
          ax44 := h.2.1
          ax45 := h.2.2.1
          ax46 := h.2.2.2 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_3, h.ax44, h.ax45, h.ax46⟩⟩

instance decidableUFOAxioms3_5 (Sig : UFOSignature3_5)
    [Decidable (UFOAxioms3_4 Sig.toUFOSignature3_4)]
    [Decidable (ax_a47 Sig)] [Decidable (ax_a48 Sig)] [Decidable (ax_a49 Sig)]
    [Decidable (ax_a50 Sig)] [Decidable (ax_a51 Sig)] [Decidable (ax_a52 Sig)] :
    Decidable (UFOAxioms3_5 Sig) :=
  decidable_of_iff
    (UFOAxioms3_4 Sig.toUFOSignature3_4 ∧ ax_a47 Sig ∧ ax_a48 Sig ∧
     ax_a49 Sig ∧ ax_a50 Sig ∧ ax_a51 Sig ∧ ax_a52 Sig)
    ⟨by
      intro h
      rcases h with ⟨h4, h47, h48, h49, h50, h51, h52⟩
      exact
        { toUFOAxioms3_4 := h4
          ax47 := h47
          ax48 := h48
          ax49 := h49
          ax50 := h50
          ax51 := h51
          ax52 := h52 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_4, h.ax47, h.ax48, h.ax49, h.ax50, h.ax51, h.ax52⟩⟩

instance decidableUFOAxioms3_6 (Sig : UFOSignature3_6)
    [Decidable (UFOAxioms3_5 Sig.toUFOSignature3_5)]
    [Decidable (ax_a53 Sig)] [Decidable (ax_a54 Sig)] [Decidable (ax_a55 Sig)] :
    Decidable (UFOAxioms3_6 Sig) :=
  decidable_of_iff
    (UFOAxioms3_5 Sig.toUFOSignature3_5 ∧ ax_a53 Sig ∧ ax_a54 Sig ∧ ax_a55 Sig)
    ⟨by
      intro h
      exact
        { toUFOAxioms3_5 := h.1
          ax53 := h.2.1
          ax54 := h.2.2.1
          ax55 := h.2.2.2 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_5, h.ax53, h.ax54, h.ax55⟩⟩

instance decidableUFOAxioms3_7 (Sig : UFOSignature3_7)
    [Decidable (UFOAxioms3_6 Sig.toUFOSignature3_6)]
    [Decidable (ax_a56 Sig)] [Decidable (ax_a57 Sig)] [Decidable (ax_a58 Sig)]
    [Decidable (ax_a59 Sig)] [Decidable (ax_a60 Sig)] [Decidable (ax_a61 Sig)] :
    Decidable (UFOAxioms3_7 Sig) :=
  decidable_of_iff
    (UFOAxioms3_6 Sig.toUFOSignature3_6 ∧ ax_a56 Sig ∧ ax_a57 Sig ∧
     ax_a58 Sig ∧ ax_a59 Sig ∧ ax_a60 Sig ∧ ax_a61 Sig)
    ⟨by
      intro h
      rcases h with ⟨h6, h56, h57, h58, h59, h60, h61⟩
      exact
        { toUFOAxioms3_6 := h6
          ax56 := h56
          ax57 := h57
          ax58 := h58
          ax59 := h59
          ax60 := h60
          ax61 := h61 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_6, h.ax56, h.ax57, h.ax58, h.ax59, h.ax60, h.ax61⟩⟩

instance decidableUFOAxioms3_8 (Sig : UFOSignature3_8)
    [Decidable (UFOAxioms3_7 Sig.toUFOSignature3_7)]
    [Decidable (ax_a62 Sig)] [Decidable (ax_a63 Sig)] [Decidable (ax_a64 Sig)] :
    Decidable (UFOAxioms3_8 Sig) :=
  decidable_of_iff
    (UFOAxioms3_7 Sig.toUFOSignature3_7 ∧ ax_a62 Sig ∧ ax_a63 Sig ∧ ax_a64 Sig)
    ⟨by
      intro h
      exact
        { toUFOAxioms3_7 := h.1
          ax62 := h.2.1
          ax63 := h.2.2.1
          ax64 := h.2.2.2 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_7, h.ax62, h.ax63, h.ax64⟩⟩

instance decidableUFOAxioms3_9 (Sig : UFOSignature3_9)
    [Decidable (UFOAxioms3_8 Sig.toUFOSignature3_8)]
    [Decidable (ax_a65 Sig)] [Decidable (ax_a66 Sig)] [Decidable (ax_a67 Sig)]
    [Decidable (ax_a68 Sig)] :
    Decidable (UFOAxioms3_9 Sig) :=
  decidable_of_iff
    (UFOAxioms3_8 Sig.toUFOSignature3_8 ∧ ax_a65 Sig ∧ ax_a66 Sig ∧
     ax_a67 Sig ∧ ax_a68 Sig)
    ⟨by
      intro h
      rcases h with ⟨h8, h65, h66, h67, h68⟩
      exact
        { toUFOAxioms3_8 := h8
          ax65 := h65
          ax66 := h66
          ax67 := h67
          ax68 := h68 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_8, h.ax65, h.ax66, h.ax67, h.ax68⟩⟩

instance decidableUFOAxioms3_10 (Sig : UFOSignature3_10)
    [Decidable (UFOAxioms3_9 Sig.toUFOSignature3_9)]
    [Decidable (ax_a69 Sig)] [Decidable (ax_a70 Sig)] [Decidable (ax_a71 Sig)]
    [Decidable (ax_a72 Sig)] [Decidable (ax_a73 Sig)] [Decidable (ax_a74 Sig)]
    [Decidable (ax_a75 Sig)] [Decidable (ax_a76 Sig)] [Decidable (ax_a77 Sig)]
    [Decidable (ax_a78 Sig)] [Decidable (ax_a79 Sig)] [Decidable (ax_a80 Sig)]
    [Decidable (ax_quaIndividualOf_endurant (Sig := Sig))] :
    Decidable (UFOAxioms3_10 Sig) :=
  decidable_of_iff
    (UFOAxioms3_9 Sig.toUFOSignature3_9 ∧ ax_a69 Sig ∧ ax_a70 Sig ∧
     ax_a71 Sig ∧ ax_a72 Sig ∧ ax_a73 Sig ∧ ax_a74 Sig ∧ ax_a75 Sig ∧
     ax_a76 Sig ∧ ax_a77 Sig ∧ ax_a78 Sig ∧ ax_a79 Sig ∧ ax_a80 Sig ∧
     ax_quaIndividualOf_endurant (Sig := Sig))
    ⟨by
      intro h
      rcases h with ⟨h9, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78,
        h79, h80, hQua⟩
      exact
        { toUFOAxioms3_9 := h9
          ax69 := h69
          ax70 := h70
          ax71 := h71
          ax72 := h72
          ax73 := h73
          ax74 := h74
          ax75 := h75
          ax76 := h76
          ax77 := h77
          ax78 := h78
          ax79 := h79
          ax80 := h80
          axQuaIndividualOfEndurant := hQua },
     by
      intro h
      exact ⟨h.toUFOAxioms3_9, h.ax69, h.ax70, h.ax71, h.ax72, h.ax73, h.ax74,
        h.ax75, h.ax76, h.ax77, h.ax78, h.ax79, h.ax80,
        h.axQuaIndividualOfEndurant⟩⟩

instance decidableUFOAxioms3_11 (Sig : UFOSignature3_11)
    [Decidable (UFOAxioms3_10 Sig.toUFOSignature3_10)]
    [Decidable (ax_a81 Sig)] [Decidable (ax_a82 Sig)] :
    Decidable (UFOAxioms3_11 Sig) :=
  decidable_of_iff
    (UFOAxioms3_10 Sig.toUFOSignature3_10 ∧ ax_a81 Sig ∧ ax_a82 Sig)
    ⟨by
      intro h
      exact
        { toUFOAxioms3_10 := h.1
          ax81 := h.2.1
          ax82 := h.2.2 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_10, h.ax81, h.ax82⟩⟩

instance decidableUFOAxioms3_12 (Sig : UFOSignature3_12)
    [Decidable (UFOAxioms3_11 Sig.toUFOSignature3_11)]
    [Decidable (ax_a83 Sig)] [Decidable (ax_a84 Sig)] [Decidable (ax_a85 Sig)]
    [Decidable (ax_a86 Sig)] [Decidable (ax_a87 Sig)] [Decidable (ax_a88 Sig)]
    [Decidable (ax_a89 Sig)] [Decidable (ax_a90 Sig)] [Decidable (ax_a91 Sig)]
    [Decidable (ax_a92 Sig)] [Decidable (ax_a93 Sig)] [Decidable (ax_a94 Sig)]
    [Decidable (ax_a95 Sig)] [Decidable (ax_a96 Sig)] [Decidable (ax_a97 Sig)]
    [Decidable (ax_a98 Sig)] [Decidable (ax_a99 Sig)] [Decidable (ax_a100 Sig)]
    [Decidable (ax_a101 Sig)] [Decidable (ax_distance_identity Sig)]
    [Decidable (ax_distance_symmetry Sig)] [Decidable (ax_distance_triangle Sig)] :
    Decidable (UFOAxioms3_12 Sig) :=
  decidable_of_iff
    (UFOAxioms3_11 Sig.toUFOSignature3_11 ∧ ax_a83 Sig ∧ ax_a84 Sig ∧
     ax_a85 Sig ∧ ax_a86 Sig ∧ ax_a87 Sig ∧ ax_a88 Sig ∧ ax_a89 Sig ∧
     ax_a90 Sig ∧ ax_a91 Sig ∧ ax_a92 Sig ∧ ax_a93 Sig ∧ ax_a94 Sig ∧
     ax_a95 Sig ∧ ax_a96 Sig ∧ ax_a97 Sig ∧ ax_a98 Sig ∧ ax_a99 Sig ∧
     ax_a100 Sig ∧ ax_a101 Sig ∧ ax_distance_identity Sig ∧
     ax_distance_symmetry Sig ∧ ax_distance_triangle Sig)
    ⟨by
      intro h
      rcases h with ⟨h11, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92,
        h93, h94, h95, h96, h97, h98, h99, h100, h101, hDI, hDS, hDT⟩
      exact
        { toUFOAxioms3_11 := h11
          ax83 := h83
          ax84 := h84
          ax85 := h85
          ax86 := h86
          ax87 := h87
          ax88 := h88
          ax89 := h89
          ax90 := h90
          ax91 := h91
          ax92 := h92
          ax93 := h93
          ax94 := h94
          ax95 := h95
          ax96 := h96
          ax97 := h97
          ax98 := h98
          ax99 := h99
          ax100 := h100
          ax101 := h101
          axDistanceIdentity := hDI
          axDistanceSymmetry := hDS
          axDistanceTriangle := hDT },
     by
      intro h
      exact ⟨h.toUFOAxioms3_11, h.ax83, h.ax84, h.ax85, h.ax86, h.ax87, h.ax88,
        h.ax89, h.ax90, h.ax91, h.ax92, h.ax93, h.ax94, h.ax95, h.ax96, h.ax97,
        h.ax98, h.ax99, h.ax100, h.ax101, h.axDistanceIdentity,
        h.axDistanceSymmetry, h.axDistanceTriangle⟩⟩

instance decidableUFOAxioms3_13 (Sig : UFOSignature3_13)
    [Decidable (UFOAxioms3_12 Sig.toUFOSignature3_12)]
    [Decidable (ax_a102 Sig)] [Decidable (ax_a103 Sig)] [Decidable (ax_a104 Sig)] :
    Decidable (UFOAxioms3_13 Sig) :=
  decidable_of_iff
    (UFOAxioms3_12 Sig.toUFOSignature3_12 ∧ ax_a102 Sig ∧ ax_a103 Sig ∧ ax_a104 Sig)
    ⟨by
      intro h
      exact
        { toUFOAxioms3_12 := h.1
          ax102 := h.2.1
          ax103 := h.2.2.1
          ax104 := h.2.2.2 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_12, h.ax102, h.ax103, h.ax104⟩⟩

instance decidableUFOAxioms4 (Sig : UFOSignature4)
    [Decidable (UFOAxioms3_13 Sig.toUFOSignature3_13)]
    [Decidable (ax_a105 Sig)] [Decidable (ax_a106 Sig)] [Decidable (ax_a107 Sig)]
    [Decidable (ax_a108 Sig)] :
    Decidable (UFOAxioms4 Sig) :=
  decidable_of_iff
    (UFOAxioms3_13 Sig.toUFOSignature3_13 ∧ ax_a105 Sig ∧ ax_a106 Sig ∧
     ax_a107 Sig ∧ ax_a108 Sig)
    ⟨by
      intro h
      rcases h with ⟨h13, h105, h106, h107, h108⟩
      exact
        { toUFOAxioms3_13 := h13
          ax105 := h105
          ax106 := h106
          ax107 := h107
          ax108 := h108 },
     by
      intro h
      exact ⟨h.toUFOAxioms3_13, h.ax105, h.ax106, h.ax107, h.ax108⟩⟩

end LeanUfo.UFO.DSL
