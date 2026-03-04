# Lean4 완전 정복 가이드 — Part 14-B: 부울 대수의 항등식과 쌍대성 — 표 5의 모든 법칙 + 곱의 합 표준형

> **Rosen 이산수학 8판 · Section 12.1 후반부 + Section 12.2 기반**
> **『Mathematics in Lean』 + Lean 4 공식화**

---

## 0. 들어가며: 이 파트에서 배울 것

Part 14-A에서는 부울 대수의 세 가지 기본 연산(보수, 합, 곱)과 부울 함수의 개념을 배웠다. 이번 파트에서는 부울 대수의 **핵심 법칙들**을 모두 정리하고, 그것을 Lean 4로 증명하는 방법을 익힌다.

이 파트에서 다루는 내용:

1. **부울 대수의 항등식**(Rosen 표 5의 모든 법칙) — 총 17가지 항등식
2. **쌍대성**(duality)의 원리 — "합↔곱, 0↔1을 바꾸면 여전히 성립"
3. **부울 대수의 추상적 정의**(정의 1) — Lean 4의 `BooleanAlgebra`
4. **곱의 합 표준형**(sum-of-products expansion / disjunctive normal form)
5. **함수적 완전성**(functional completeness): NAND와 NOR 하나면 충분하다!
6. XOR 연산과 그 성질

> 💡 **핵심 메시지**: 부울 대수, 명제 논리, 집합론은 모두 **같은 구조의 다른 표현**이다. 하나를 알면 나머지 둘을 거의 공짜로 얻는다!

---

## 1. 부울 대수의 항등식 — Rosen 표 5 완전 정복

다음은 Rosen 12.1절 **표 5**의 모든 항등 관계이다. 각 법칙을 하나씩 자세히 살펴보자.

### 1.1 이중 보수 법칙 (Law of Double Complement)

$$\overline{\overline{x}} = x$$

"두 번 뒤집으면 원래대로 돌아온다."

> 🔦 **비유**: 불을 한 번 끄고(보수), 다시 끄면(보수) 원래 상태로 돌아온다.

```lean
-- Bool에서의 증명
example : ∀ x : Bool, !(!x) = x := by decide

-- 추상 BooleanAlgebra에서
variable {α : Type*} [BooleanAlgebra α] (x : α)
#check (compl_compl x : xᶜᶜ = x)
```

### 1.2 멱등 법칙 (Idempotent Laws)

$$x + x = x, \quad x \cdot x = x$$

"같은 것을 합하거나 곱해도 자기 자신이다."

> 🍕 **비유**: "피자를 시키거나 피자를 시키거나" — 결국 피자를 시킨 것이다.

```lean
example : ∀ x : Bool, x || x = x := by decide
example : ∀ x : Bool, x && x = x := by decide

variable {α : Type*} [BooleanAlgebra α] (x : α)
#check (sup_idem : x ⊔ x = x)
#check (inf_idem : x ⊓ x = x)
```

### 1.3 항등 법칙 (Identity Laws)

$$x + 0 = x, \quad x \cdot 1 = x$$

"0을 OR하거나, 1을 AND해도 변하지 않는다."

```lean
example : ∀ x : Bool, x || false = x := by decide
example : ∀ x : Bool, x && true = x := by decide

variable {α : Type*} [BooleanAlgebra α] (x : α)
#check (sup_bot_eq : x ⊔ ⊥ = x)
#check (inf_top_eq : x ⊓ ⊤ = x)
```

### 1.4 지배 법칙 (Domination Laws)

$$x + 1 = 1, \quad x \cdot 0 = 0$$

"1을 OR하면 무조건 1, 0을 AND하면 무조건 0."

```lean
example : ∀ x : Bool, x || true = true := by decide
example : ∀ x : Bool, x && false = false := by decide

variable {α : Type*} [BooleanAlgebra α] (x : α)
#check (sup_top_eq : x ⊔ ⊤ = ⊤)
#check (inf_bot_eq : x ⊓ ⊥ = ⊥)
```

### 1.5 교환 법칙 (Commutative Laws)

$$x + y = y + x, \quad x \cdot y = y \cdot x$$

```lean
example : ∀ x y : Bool, x || y = y || x := by decide
example : ∀ x y : Bool, x && y = y && x := by decide

variable {α : Type*} [BooleanAlgebra α] (x y : α)
#check (sup_comm : x ⊔ y = y ⊔ x)
#check (inf_comm : x ⊓ y = y ⊓ x)
```

### 1.6 결합 법칙 (Associative Laws)

$$x + (y + z) = (x + y) + z, \quad x \cdot (y \cdot z) = (x \cdot y) \cdot z$$

```lean
example : ∀ x y z : Bool, x || (y || z) = (x || y) || z := by decide
example : ∀ x y z : Bool, x && (y && z) = (x && y) && z := by decide

variable {α : Type*} [BooleanAlgebra α] (x y z : α)
#check (sup_assoc : x ⊔ (y ⊔ z) = x ⊔ y ⊔ z)
#check (inf_assoc : x ⊓ (y ⊓ z) = x ⊓ y ⊓ z)
```

### 1.7 분배 법칙 (Distributive Laws) ⭐

이것이 핵심이다! **두 가지** 분배 법칙이 있다:

$$x + (y \cdot z) = (x + y) \cdot (x + z) \quad \text{← 부울 대수 고유!}$$
$$x \cdot (y + z) = (x \cdot y) + (x \cdot z) \quad \text{← 일반 수학에도 있음}$$

> ⚠️ **주의!** 첫 번째 법칙은 일반 수학에서는 성립하지 않는다! $2 + (3 \times 4) = 14$이지만 $(2+3) \times (2+4) = 30$이다. 부울 대수에서만 성립하는 특별한 법칙이다.

```lean
-- 첫 번째 분배 법칙 (부울 대수 고유!)
example : ∀ x y z : Bool, x || (y && z) = (x || y) && (x || z) := by decide

-- 두 번째 분배 법칙 (일반 수학과 동일한 형태)
example : ∀ x y z : Bool, x && (y || z) = (x && y) || (x && z) := by decide

variable {α : Type*} [BooleanAlgebra α] (x y z : α)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
```

### 1.8 드 모르간 법칙 (De Morgan's Laws)

$$\overline{x + y} = \overline{x} \cdot \overline{y}, \quad \overline{x \cdot y} = \overline{x} + \overline{y}$$

> 🏠 **비유**: "집에 있거나 학교에 있다"의 부정 = "집에도 없**고** 학교에도 없다" (OR의 부정 = AND).
> "집에 있**고** 학교에 있다"의 부정 = "집에 없**거나** 학교에 없다" (AND의 부정 = OR).

```lean
example : ∀ x y : Bool, !(x || y) = (!x) && (!y) := by decide
example : ∀ x y : Bool, !(x && y) = (!x) || (!y) := by decide

variable {α : Type*} [BooleanAlgebra α] (x y : α)
#check (compl_sup : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ)
#check (compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ)
```

### 1.9 흡수 법칙 (Absorption Laws)

$$x + (x \cdot y) = x, \quad x \cdot (x + y) = x$$

> 🌊 **비유**: 큰 바다($x$)에 물 한 컵($xy$)을 더해도 바다는 그대로이다.

**Rosen 예제 10**의 증명 (표 5의 항등식만 사용):

| 단계 | 식 | 사용한 법칙 |
|------|---|---------|
| 시작 | $x(x + y)$ | |
| 1 | $(x + 0)(x + y)$ | 항등 법칙의 역: $x = x + 0$ |
| 2 | $x + 0 \cdot y$ | 분배 법칙 (첫 번째 형태의 역) |
| 3 | $x + y \cdot 0$ | 교환 법칙 |
| 4 | $x + 0$ | 지배 법칙: $y \cdot 0 = 0$ |
| 5 | $x$ | 항등 법칙: $x + 0 = x$ |

```lean
example : ∀ x y : Bool, x || (x && y) = x := by decide
example : ∀ x y : Bool, x && (x || y) = x := by decide

variable {α : Type*} [BooleanAlgebra α] (x y : α)
#check (sup_inf_self : x ⊔ x ⊓ y = x)
#check (inf_sup_self : x ⊓ (x ⊔ y) = x)
```

### 1.10 단위 성질과 제로 성질 (Unit & Zero Properties)

$$x + \overline{x} = 1, \quad x \cdot \overline{x} = 0$$

> 🎭 **비유**: "비가 오거나 비가 안 오거나" — 반드시 참(1). "비가 오고 비가 안 온다" — 불가능(0).

```lean
example : ∀ x : Bool, x || (!x) = true := by decide
example : ∀ x : Bool, x && (!x) = false := by decide

variable {α : Type*} [BooleanAlgebra α] (x : α)
#check (sup_compl_eq_top : x ⊔ xᶜ = ⊤)
#check (inf_compl_eq_bot : x ⊓ xᶜ = ⊥)
```

---

## 2. 전체 항등식 대응표 (Rosen 표 5)

| 법칙 | 부울 대수 | Lean 4 (`Bool`) | Lean 4 (추상) |
|-----|---------|----------------|-------------|
| **이중 보수** | $\overline{\overline{x}} = x$ | `!(!x) = x` | `compl_compl` |
| **멱등**(합) | $x+x=x$ | `x \|\| x = x` | `sup_idem` |
| **멱등**(곱) | $x \cdot x = x$ | `x && x = x` | `inf_idem` |
| **항등**(합) | $x+0=x$ | `x \|\| false = x` | `sup_bot_eq` |
| **항등**(곱) | $x \cdot 1=x$ | `x && true = x` | `inf_top_eq` |
| **지배**(합) | $x+1=1$ | `x \|\| true = true` | `sup_top_eq` |
| **지배**(곱) | $x \cdot 0=0$ | `x && false = false` | `inf_bot_eq` |
| **교환**(합) | $x+y=y+x$ | `x \|\| y = y \|\| x` | `sup_comm` |
| **교환**(곱) | $xy=yx$ | `x && y = y && x` | `inf_comm` |
| **결합**(합) | $x+(y+z)=(x+y)+z$ | 동일 | `sup_assoc` |
| **결합**(곱) | $x(yz)=(xy)z$ | 동일 | `inf_assoc` |
| **분배**(합/곱) | $x+(yz)=(x+y)(x+z)$ | 동일 | `sup_inf_left` |
| **분배**(곱/합) | $x(y+z)=xy+xz$ | 동일 | `inf_sup_left` |
| **드모르간**(합) | $\overline{x+y}=\overline{x}\cdot\overline{y}$ | 동일 | `compl_sup` |
| **드모르간**(곱) | $\overline{xy}=\overline{x}+\overline{y}$ | 동일 | `compl_inf` |
| **흡수**(합) | $x+xy=x$ | 동일 | `sup_inf_self` |
| **흡수**(곱) | $x(x+y)=x$ | 동일 | `inf_sup_self` |
| **단위** | $x+\overline{x}=1$ | `x \|\| (!x) = true` | `sup_compl_eq_top` |
| **제로** | $x \cdot \overline{x}=0$ | `x && (!x) = false` | `inf_compl_eq_bot` |

---

## 3. 쌍대성의 원리 — "합↔곱, 0↔1을 바꿔도 성립"

### 3.1 쌍대란?

부울 식의 **쌍대**(dual)는 다음을 수행하여 얻는다:
- $+$(OR) ↔ $\cdot$(AND) 서로 교환
- $0$ ↔ $1$ 서로 교환
- 변수와 보수는 **그대로**

**예제 11** (Rosen):
- $x(y+0)$의 쌍대: $x + (y \cdot 1)$
- $x \cdot 1 + (y + z)$의 쌍대: $(x + 0)(y \cdot z)$

### 3.2 쌍대성의 원리

> **정리**: 부울 항등식이 성립하면, 양변의 쌍대를 취한 것도 항등식으로 성립한다.

이것이 표 5에서 항등식들이 **짝을 지어** 나타나는 이유이다! 거울처럼 $+$와 $\cdot$, $0$과 $1$을 바꾸면 다른 한 쪽 법칙이 나온다.

**예제 12** (Rosen): $x(x+y) = x$의 쌍대 → $x + xy = x$ (두 흡수 법칙이 쌍대!)

```lean
-- 흡수 법칙의 쌍대 쌍
example : ∀ x y : Bool, x && (x || y) = x := by decide  -- 원본
example : ∀ x y : Bool, x || (x && y) = x := by decide  -- 쌍대
```

---

## 4. 부울 대수의 추상적 정의 — Lean 4의 `BooleanAlgebra`

### 4.1 Rosen의 정의 1

**부울 대수**(Boolean Algebra)는 집합 $B$와 연산 $\lor$, $\land$, 보수, 원소 0, 1이 다음을 만족하는 것이다:

1. **항등 법칙**: $x \lor 0 = x$, $x \land 1 = x$
2. **보수 법칙**: $x \lor \overline{x} = 1$, $x \land \overline{x} = 0$
3. **결합 법칙**: $(x \lor y) \lor z = x \lor (y \lor z)$, 곱도 마찬가지
4. **교환 법칙**: $x \lor y = y \lor x$, 곱도 마찬가지
5. **분배 법칙**: $x \lor (y \land z) = (x \lor y) \land (x \lor z)$, 곱도 마찬가지

이 5가지만으로 나머지 모든 법칙을 **유도**할 수 있다!

### 4.2 세 가지 부울 대수의 인스턴스

| 구조 | ∨ (합) | ∧ (곱) | 보수 | 0 | 1 |
|------|-------|-------|------|---|---|
| **{0,1}** | + | · | $\overline{\phantom{x}}$ | 0 | 1 |
| **명제 논리** | ∨ | ∧ | ¬ | F | T |
| **집합론** | ∪ | ∩ | 여집합 | ∅ | 전체집합 |
| **Lean 4** | `⊔` | `⊓` | `ᶜ` | `⊥` | `⊤` |

하나를 증명하면 나머지에도 자동으로 적용된다!

```lean
variable {α : Type*} [BooleanAlgebra α] (x y z : α)

-- 사용 가능한 정리들
example : x ⊓ xᶜ = ⊥ := inf_compl_eq_bot
example : x ⊔ xᶜ = ⊤ := sup_compl_eq_top
example : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z := inf_sup_left x y z
example : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z) := sup_inf_left x y z
```

---

## 5. 곱의 합 표준형 — 진리표에서 부울 식 만들기

### 5.1 최소항이란?

**최소항**(minterm)은 모든 변수가 정확히 한 번씩 나타나는 부울 곱이다.

변수 $x_1, x_2, \ldots, x_n$에 대해, 최소항에서 각 $y_i$는:
- $x_i = 1$이면 $y_i = x_i$ (변수 그대로)
- $x_i = 0$이면 $y_i = \overline{x_i}$ (보수)

> 🎯 **핵심**: 최소항은 **딱 하나의 입력 조합**에서만 1이 되고, 나머지는 모두 0이다.

**예** (Rosen 예제 2): $x_1 = x_3 = 0, x_2 = x_4 = x_5 = 1$일 때 1이 되는 최소항:
$$\overline{x_1} \cdot x_2 \cdot \overline{x_3} \cdot x_4 \cdot x_5$$

### 5.2 곱의 합 표준형 만드는 법

1. 진리표에서 함수값이 **1인 행**을 찾는다
2. 각 행에 대응하는 **최소항**을 만든다
3. 모든 최소항을 **부울 합**(OR)으로 연결한다

**예제** (Rosen 예제 3): $F(x, y, z) = (x + y)\overline{z}$의 곱의 합 표준형:

| $x$ | $y$ | $z$ | $(x+y)\overline{z}$ | 최소항 |
|-----|-----|-----|---------------------|------|
| 1   | 1   | 0   | **1** | $xy\overline{z}$ |
| 1   | 0   | 0   | **1** | $x\overline{y}\overline{z}$ |
| 0   | 1   | 0   | **1** | $\overline{x}y\overline{z}$ |
| (나머지) | | | 0 | — |

$$F = xy\overline{z} + x\overline{y}\overline{z} + \overline{x}y\overline{z}$$

```lean
def F_orig (x y z : Bool) : Bool := (x || y) && (!z)

def F_dnf (x y z : Bool) : Bool :=
  (x && y && !z) || (x && !y && !z) || (!x && y && !z)

-- 동치 검증
example : ∀ x y z : Bool, F_orig x y z = F_dnf x y z := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
```

---

## 6. 함수적 완전성 — NAND 하나면 모든 것을 만든다!

### 6.1 함수적 완전이란?

연산자 집합이 **함수적으로 완전**(functionally complete)하다 = 그 연산자들만으로 **모든** 부울 함수를 표현 가능.

- $\{+, \cdot, \overline{\phantom{x}}\}$ → 완전 (곱의 합 표준형으로 증명)
- $\{\cdot, \overline{\phantom{x}}\}$ → 완전 (드 모르간: $x + y = \overline{\overline{x} \cdot \overline{y}}$)
- $\{+, \overline{\phantom{x}}\}$ → 완전 (드 모르간: $x \cdot y = \overline{\overline{x} + \overline{y}}$)
- $\{+, \cdot\}$ → **불완전!** ($\overline{x}$를 만들 수 없다)

### 6.2 NAND — 하나의 연산으로 모든 것을!

**NAND**(|): $x | y = \overline{x \cdot y}$

| $x$ | $y$ | $x \mid y$ |
|-----|-----|-----------|
| 1   | 1   | 0 |
| 1   | 0   | 1 |
| 0   | 1   | 1 |
| 0   | 0   | 1 |

NAND로 NOT, AND, OR을 모두 만들 수 있다:

```lean
def nand (x y : Bool) : Bool := !(x && y)

-- NOT x = x NAND x
example : ∀ x : Bool, nand x x = !x := by
  intro x; cases x <;> rfl

-- AND x y = (x NAND y) NAND (x NAND y)
example : ∀ x y : Bool, nand (nand x y) (nand x y) = (x && y) := by
  intro x y; cases x <;> cases y <;> rfl

-- OR x y = (x NAND x) NAND (y NAND y)
example : ∀ x y : Bool, nand (nand x x) (nand y y) = (x || y) := by
  intro x y; cases x <;> cases y <;> rfl
```

### 6.3 NOR — 이것도 하나로 충분!

**NOR**(↓): $x \downarrow y = \overline{x + y}$

```lean
def nor (x y : Bool) : Bool := !(x || y)

-- NOT x = x NOR x
example : ∀ x : Bool, nor x x = !x := by
  intro x; cases x <;> rfl

-- OR x y = (x NOR y) NOR (x NOR y)
example : ∀ x y : Bool, nor (nor x y) (nor x y) = (x || y) := by
  intro x y; cases x <;> cases y <;> rfl

-- AND x y = (x NOR x) NOR (y NOR y)
example : ∀ x y : Bool, nor (nor x x) (nor y y) = (x && y) := by
  intro x y; cases x <;> cases y <;> rfl
```

---

## 7. XOR 연산 — 배타적 논리합

**XOR**(⊕): "둘 중 정확히 하나만 1일 때 1"

| $x$ | $y$ | $x \oplus y$ |
|-----|-----|-------------|
| 1   | 1   | 0 |
| 1   | 0   | 1 |
| 0   | 1   | 1 |
| 0   | 0   | 0 |

```lean
-- XOR 기본 성질
example : ∀ x : Bool, xor x false = x := by decide        -- x ⊕ 0 = x
example : ∀ x : Bool, xor x true = !x := by decide         -- x ⊕ 1 = x̄
example : ∀ x : Bool, xor x x = false := by decide         -- x ⊕ x = 0
example : ∀ x : Bool, xor x (!x) = true := by decide       -- x ⊕ x̄ = 1

-- 교환법칙, 결합법칙
example : ∀ x y : Bool, xor x y = xor y x := by decide
example : ∀ x y z : Bool, xor (xor x y) z = xor x (xor y z) := by decide

-- 기본 연산으로 표현
-- x ⊕ y = xȳ + x̄y
example : ∀ x y : Bool, xor x y = (x && !y) || (!x && y) := by decide
-- x ⊕ y = (x + y) · (x̄ȳ) = (x + y) · ¬(xy)
example : ∀ x y : Bool, xor x y = (x || y) && (!(x && y)) := by decide
```

---

## 8. 연습문제: 괄호 채우기 (Skeleton)

### 연습 8.1: 항등식 `decide`로 증명

```lean
-- (a) 멱등 법칙
example : ∀ x : Bool, x || x = ⟨YOUR_ANSWER⟩ := by ⟨YOUR_TACTIC⟩

-- (b) 드 모르간 법칙
example : ∀ x y : Bool, !(x || y) = ⟨YOUR_EXPRESSION⟩ := by ⟨YOUR_TACTIC⟩

-- (c) 흡수 법칙
example : ∀ x y : Bool, x || (x && y) = ⟨YOUR_ANSWER⟩ := by ⟨YOUR_TACTIC⟩

-- (d) 지배 법칙
example : ∀ x : Bool, x && false = ⟨YOUR_ANSWER⟩ := by ⟨YOUR_TACTIC⟩
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x : Bool, x || x = x := by decide
example : ∀ x y : Bool, !(x || y) = (!x) && (!y) := by decide
example : ∀ x y : Bool, x || (x && y) = x := by decide
example : ∀ x : Bool, x && false = false := by decide
```

</details>

### 연습 8.2: `cases`로 직접 증명

```lean
-- (a) 단위 성질: x || (!x) = true
example : ∀ x : Bool, x || (!x) = true := by
  sorry

-- (b) 제로 성질: x && (!x) = false
example : ∀ x : Bool, x && (!x) = false := by
  sorry

-- (c) 드 모르간 (곱): !(x && y) = (!x) || (!y)
example : ∀ x y : Bool, !(x && y) = (!x) || (!y) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x : Bool, x || (!x) = true := by
  intro x; cases x <;> rfl

example : ∀ x : Bool, x && (!x) = false := by
  intro x; cases x <;> rfl

example : ∀ x y : Bool, !(x && y) = (!x) || (!y) := by
  intro x y; cases x <;> cases y <;> rfl
```

**해설**: `cases x`는 `x : Bool`을 `true`와 `false` 두 경우로 나눈다. `<;>`는 "모든 목표에 다음 전략 적용"이다.

</details>

### 연습 8.3: 분배 법칙 (부울 대수 고유)

```lean
-- x || (y && z) = (x || y) && (x || z)
-- 일반 수학에는 없는 부울 대수만의 분배 법칙!
example : ∀ x y z : Bool, x || (y && z) = (x || y) && (x || z) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y z : Bool, x || (y && z) = (x || y) && (x || z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
```

3변수이므로 $2^3 = 8$가지 경우를 확인한다.

</details>

### 연습 8.4: NAND/NOR 표현

```lean
-- (a) NAND로 NOT 만들기
-- 빈칸을 채우시오: nand x ⟨?⟩ = !x
example : ∀ x : Bool, nand x x = !x := by
  sorry

-- (b) NOR로 AND 만들기
-- nor (nor x x) (nor y y) = x && y 를 증명하시오
example : ∀ x y : Bool, nor (nor x x) (nor y y) = (x && y) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x : Bool, nand x x = !x := by
  intro x; cases x <;> rfl

example : ∀ x y : Bool, nor (nor x x) (nor y y) = (x && y) := by
  intro x y; cases x <;> cases y <;> rfl
```

</details>

### 연습 8.5: 곱의 합 표준형 구하기

```lean
-- F(x, y) = x + y 의 곱의 합 표준형을 만들고 동치를 증명하라

-- 진리표:
-- x=1, y=1 → F=1 → 최소항: x·y       (true && true)
-- x=1, y=0 → F=1 → 최소항: x·ȳ      (true && !false)
-- x=0, y=1 → F=1 → 최소항: x̄·y      (!false && true)
-- x=0, y=0 → F=0 → (포함 안 함)

def F_or_dnf (x y : Bool) : Bool :=
  (x && y) || (x && !y) || (!x && y)

example : ∀ x y : Bool, (x || y) = F_or_dnf x y := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y : Bool, (x || y) = F_or_dnf x y := by
  intro x y; cases x <;> cases y <;> rfl
```

</details>

---

## 9. 도전 연습: 추상 `BooleanAlgebra`에서 증명

`decide`나 `cases`가 아닌, **추상적** 부울 대수에서 항등식을 증명해 보자.

### 연습 9.1: 흡수 법칙을 공리로부터 증명

```lean
variable {α : Type*} [BooleanAlgebra α]

-- x ⊓ (x ⊔ y) = x 를 증명하라
-- Rosen 예제 10의 추상 버전
-- 힌트: inf_sup_self 라는 정리가 이미 있지만, 직접 증명해 보자
-- 사용 가능: le_antisymm, inf_le_left, le_inf, le_refl, le_sup_left
example (x y : α) : x ⊓ (x ⊔ y) = x := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example (x y : α) : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · -- x ⊓ (x ⊔ y) ≤ x
    exact inf_le_left
  · -- x ≤ x ⊓ (x ⊔ y)
    exact le_inf le_rfl le_sup_left

-- 또는 한 줄로:
example (x y : α) : x ⊓ (x ⊔ y) = x := inf_sup_self
```

**해설**:
- `le_antisymm`으로 양방향 부등식을 보인다: $a \le b$이고 $b \le a$이면 $a = b$
- 왼쪽→오른쪽: `inf_le_left`로 $x \sqcap (x \sqcup y) \le x$
- 오른쪽→왼쪽: `le_inf`로 $x \le x$이고 $x \le x \sqcup y$이므로 $x \le x \sqcap (x \sqcup y)$

</details>

### 연습 9.2: 드 모르간 법칙 확인

```lean
variable {α : Type*} [BooleanAlgebra α]

-- Mathlib의 compl_sup를 사용하여 드 모르간 법칙을 "사용"해 보자
example (x y : α) : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ := by
  sorry  -- 힌트: exact compl_sup
```

<details>
<summary>📝 답 보기</summary>

```lean
example (x y : α) : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ := compl_sup
example (x y : α) : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ := compl_inf
```

</details>

### 연습 9.3: Rosen 예제 9 — 부울 항등식을 논리적 동치로 변환

```lean
-- 분배 법칙 x + yz = (x + y)(x + z) 를
-- 명제 논리로 바꾸면: p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)

-- Lean 4의 Prop에서 이것을 증명하라
example (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · intro h
    rcases h with hp | ⟨hq, hr⟩
    · exact ⟨Or.inl hp, Or.inl hp⟩
    · exact ⟨Or.inr hq, Or.inr hr⟩
  · intro ⟨hpq, hpr⟩
    rcases hpq with hp | hq
    · exact Or.inl hp
    · rcases hpr with hp | hr
      · exact Or.inl hp
      · exact Or.inr ⟨hq, hr⟩
```

**해설**: 이것은 `Bool`이 아닌 `Prop`에서의 증명이므로 `decide`를 쓸 수 없다. 논리적 추론으로 직접 증명해야 한다. `rcases`로 경우를 나누고, `Or.inl`, `Or.inr`로 목표를 구성한다.

</details>

---

## 10. 핵심 요약

| 개념 | 핵심 |
|------|------|
| **항등식** (표 5) | 17가지 법칙, `decide`로 자동 증명 가능 |
| **쌍대성** | +↔·, 0↔1 교환하면 새 항등식 |
| **추상 정의** | `BooleanAlgebra` = 5가지 공리 |
| **곱의 합 표준형** | 모든 부울 함수 = 최소항들의 OR |
| **함수적 완전** | {+, ·, ¬} 또는 {NAND} 또는 {NOR} 하나면 충분 |
| **XOR** | 정확히 하나만 1일 때 1, 교환·결합 성립 |

---

## 다음 파트 예고

**Part 14-C**에서는:
- **논리 게이트**(logic gates): 인버터, OR 게이트, AND 게이트
- **회로 설계**: 투표기, 조명 제어, 가산기(반가산기, 전가산기)
- **회로의 최소화**: 카르노맵과 퀸-맥클러스키 방법
- Lean 4로 회로를 모델링하고 검증하는 방법
