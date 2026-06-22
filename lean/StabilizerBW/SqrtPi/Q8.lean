import StabilizerBW.SqrtPi.Z8Ring

/-!
# The cyclotomic field `ℚ[ζ₈]` as the denotation target

The free `√Π` generator `V` (a square root of the swap `X`) has denotation
`V = (1/√2)·[[ζ, ζ⁷],[ζ⁷, ζ]]`, whose entries involve `1/√2`.  To denote the whole
syntax faithfully we work over `ℚ[ζ₈]`, modelled concretely as rational 4-tuples
`a + b·ζ + c·ζ² + d·ζ³`, with the ring embedding `ℤ[ζ₈] ↪ ℚ[ζ₈]`.
-/

set_option maxRecDepth 4000

namespace Pi3

/-- An element `a + b·ζ + c·ζ² + d·ζ³` of `ℚ[ζ₈]`, with `ζ⁴ = -1`. -/
@[ext] structure Q8 where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
deriving DecidableEq

namespace Q8

instance : Zero Q8 := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Q8 := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add Q8 := ⟨fun p q => ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d⟩⟩
instance : Neg Q8 := ⟨fun p => ⟨-p.a, -p.b, -p.c, -p.d⟩⟩
instance : Sub Q8 := ⟨fun p q => ⟨p.a - q.a, p.b - q.b, p.c - q.c, p.d - q.d⟩⟩
instance : Mul Q8 := ⟨fun p q =>
  ⟨p.a * q.a - (p.b * q.d + p.c * q.c + p.d * q.b),
   (p.a * q.b + p.b * q.a) - (p.c * q.d + p.d * q.c),
   (p.a * q.c + p.b * q.b + p.c * q.a) - p.d * q.d,
   p.a * q.d + p.b * q.c + p.c * q.b + p.d * q.a⟩⟩

@[simp] lemma zero_a : (0 : Q8).a = 0 := rfl
@[simp] lemma zero_b : (0 : Q8).b = 0 := rfl
@[simp] lemma zero_c : (0 : Q8).c = 0 := rfl
@[simp] lemma zero_d : (0 : Q8).d = 0 := rfl
@[simp] lemma one_a : (1 : Q8).a = 1 := rfl
@[simp] lemma one_b : (1 : Q8).b = 0 := rfl
@[simp] lemma one_c : (1 : Q8).c = 0 := rfl
@[simp] lemma one_d : (1 : Q8).d = 0 := rfl
@[simp] lemma add_a (p q : Q8) : (p + q).a = p.a + q.a := rfl
@[simp] lemma add_b (p q : Q8) : (p + q).b = p.b + q.b := rfl
@[simp] lemma add_c (p q : Q8) : (p + q).c = p.c + q.c := rfl
@[simp] lemma add_d (p q : Q8) : (p + q).d = p.d + q.d := rfl
@[simp] lemma neg_a (p : Q8) : (-p).a = -p.a := rfl
@[simp] lemma neg_b (p : Q8) : (-p).b = -p.b := rfl
@[simp] lemma neg_c (p : Q8) : (-p).c = -p.c := rfl
@[simp] lemma neg_d (p : Q8) : (-p).d = -p.d := rfl
@[simp] lemma sub_a (p q : Q8) : (p - q).a = p.a - q.a := rfl
@[simp] lemma sub_b (p q : Q8) : (p - q).b = p.b - q.b := rfl
@[simp] lemma sub_c (p q : Q8) : (p - q).c = p.c - q.c := rfl
@[simp] lemma sub_d (p q : Q8) : (p - q).d = p.d - q.d := rfl
@[simp] lemma mul_a (p q : Q8) :
    (p * q).a = p.a * q.a - (p.b * q.d + p.c * q.c + p.d * q.b) := rfl
@[simp] lemma mul_b (p q : Q8) :
    (p * q).b = (p.a * q.b + p.b * q.a) - (p.c * q.d + p.d * q.c) := rfl
@[simp] lemma mul_c (p q : Q8) :
    (p * q).c = (p.a * q.c + p.b * q.b + p.c * q.a) - p.d * q.d := rfl
@[simp] lemma mul_d (p q : Q8) :
    (p * q).d = p.a * q.d + p.b * q.c + p.c * q.b + p.d * q.a := rfl

instance : CommRing Q8 where
  add_assoc := by intro a b c; ext <;> simp <;> ring
  zero_add := by intro a; ext <;> simp
  add_zero := by intro a; ext <;> simp
  add_comm := by intro a b; ext <;> simp <;> ring
  left_distrib := by intro a b c; ext <;> simp <;> ring
  right_distrib := by intro a b c; ext <;> simp <;> ring
  zero_mul := by intro a; ext <;> simp
  mul_zero := by intro a; ext <;> simp
  mul_assoc := by intro a b c; ext <;> simp <;> ring
  one_mul := by intro a; ext <;> simp
  mul_one := by intro a; ext <;> simp
  mul_comm := by intro a b; ext <;> simp <;> ring
  neg_add_cancel := by intro a; ext <;> simp
  sub_eq_add_neg := by intro a b; ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The ring embedding `ℤ[ζ₈] ↪ ℚ[ζ₈]`. -/
def ofZ8 (z : Z8) : Q8 := ⟨(z.a : ℚ), (z.b : ℚ), (z.c : ℚ), (z.d : ℚ)⟩

@[simp] lemma ofZ8_a (z : Z8) : (ofZ8 z).a = (z.a : ℚ) := rfl
@[simp] lemma ofZ8_b (z : Z8) : (ofZ8 z).b = (z.b : ℚ) := rfl
@[simp] lemma ofZ8_c (z : Z8) : (ofZ8 z).c = (z.c : ℚ) := rfl
@[simp] lemma ofZ8_d (z : Z8) : (ofZ8 z).d = (z.d : ℚ) := rfl

/-- `ofZ8` as a ring homomorphism. -/
def ofZ8Hom : Z8 →+* Q8 where
  toFun := ofZ8
  map_one' := by ext <;> simp [ofZ8]
  map_mul' := by intro x y; ext <;> simp [ofZ8]
  map_zero' := by ext <;> simp [ofZ8]
  map_add' := by intro x y; ext <;> simp [ofZ8]

@[simp] lemma ofZ8Hom_apply (z : Z8) : ofZ8Hom z = ofZ8 z := rfl

lemma ofZ8_injective : Function.Injective ofZ8 := by
  intro x y h
  have ha := congrArg Q8.a h
  have hb := congrArg Q8.b h
  have hc := congrArg Q8.c h
  have hd := congrArg Q8.d h
  simp only [ofZ8_a, ofZ8_b, ofZ8_c, ofZ8_d, Int.cast_inj] at ha hb hc hd
  ext <;> assumption

/-- `√2 = ζ - ζ³ ∈ ℤ[ζ₈]`. -/
def sqrt2 : Q8 := ⟨0, 1, 0, -1⟩
/-- `1/√2 = (ζ - ζ³)/2`. -/
def invSqrt2 : Q8 := ⟨0, 1/2, 0, -1/2⟩

lemma sqrt2_sq : sqrt2 * sqrt2 = 1 + 1 := by
  ext <;> simp only [sqrt2, mul_a, mul_b, mul_c, mul_d, add_a, add_b, add_c, add_d,
    one_a, one_b, one_c, one_d] <;> norm_num

lemma invSqrt2_mul_sqrt2 : invSqrt2 * sqrt2 = 1 := by
  ext <;> simp only [invSqrt2, sqrt2, mul_a, mul_b, mul_c, mul_d, one_a, one_b, one_c, one_d] <;>
    norm_num

end Q8

end Pi3
