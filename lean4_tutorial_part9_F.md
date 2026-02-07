# Lean 4 튜토리얼 — Part 9-F: 일반화된 순열과 조합 (Generalized Permutations and Combinations)

> **시리즈 위치**: Rosen 이산수학 8판 §6.5  
> **선수 지식**: Part 9-D (순열과 조합), Part 9-E (이항 정리)  
> **목표**: **반복을 허용하는 순열**, **구별할 수 없는 원소의 순열**, **중복 조합**을 Lean 4로 다룬다.

---

## 9F.0 이 장에서 배울 것

지금까지 배운 순열과 조합에서는 모든 원소가 **서로 다르고** 각 원소를 **한 번만** 사용할 수 있었다. 하지만 현실에서는 반복 사용이 가능하거나 구별할 수 없는 원소가 있는 경우가 많다. 이 장에서는 이러한 일반화된 상황을 다룬다.

---

## 9F.1 **반복을 허용하는 순열**(Permutations with Repetition)

### 9F.1.1 기본 원리

> **정리**: n개의 원소를 가진 집합에서 **반복을 허용하여** r개를 뽑아 순서대로 나열하는 방법의 수는 **nʳ**이다.

각 위치마다 n가지 선택이 있고, 총 r개의 위치가 있으므로 곱셈 법칙에 의해 n × n × ··· × n = nʳ이다.

### 9F.1.2 교재 예제 1: 대문자 알파벳 문자열

> **문제**: 영어 대문자 알파벳으로 이루어진 길이 r의 문자열은 모두 몇 가지인가?

**풀이**: 26개의 알파벳에서 반복을 허용하여 r개를 선택하므로 26ʳ가지이다.

```lean
-- 길이 3: 26³ = 17576
example : 26^3 = 17576 := by norm_num

-- 길이 4: 26⁴ = 456976
example : 26^4 = 456976 := by norm_num
```

### 9F.1.3 Lean 4에서의 표현

Lean 4에서 반복 허용 순열은 **함수**로 표현된다. `Fin r → Fin n`이 바로 "n개에서 반복 허용하여 r개를 나열"하는 것이다.

```lean
import Mathlib

-- 함수의 수 = n^r
example (n : ℕ) : Fintype.card (Fin 3 → Fin n) = n^3 := by simp

-- 구체적인 예
example : Fintype.card (Fin 3 → Fin 2) = 8 := by simp     -- 2³ = 8
example : Fintype.card (Fin 4 → Fin 10) = 10000 := by simp -- 10⁴ = 10000
```

**비교표**:

| 유형 | Lean 4 타입 | 수 |
|------|-----------|-----|
| 반복 허용 순열 | `Fin r → Fin n` (모든 함수) | nʳ |
| 반복 불허 순열 | 단사 함수 `Fin r ↪ Fin n` | P(n, r) |

---

## 9F.2 **구별할 수 없는 원소의 순열**

### 9F.2.1 문제 상황

'SUCCESS'라는 단어의 문자를 재배열하는 경우의 수는? 단순히 7! = 5040이 아니다. 왜냐하면 S가 3개, C가 2개 있어서, 같은 문자끼리 자리를 바꿔도 **같은 배열**이 되기 때문이다.

### 9F.2.2 **다항 계수**(Multinomial Coefficient)

> **정리**: n개의 원소가 있고, 그 중 같은 것이 각각 n₁개, n₂개, ..., nₖ개씩 있을 때 (n₁ + n₂ + ··· + nₖ = n), 이들의 순열의 수는  
> $$\frac{n!}{n_1! \cdot n_2! \cdot \cdots \cdot n_k!}$$

이것을 **다항 계수**(multinomial coefficient)라고 한다.

### 9F.2.3 예: SUCCESS의 재배열

SUCCESS에는 7개의 문자가 있다: S(3개), U(1개), C(2개), E(1개)

$$\frac{7!}{3! \cdot 1! \cdot 2! \cdot 1!} = \frac{5040}{6 \cdot 1 \cdot 2 \cdot 1} = \frac{5040}{12} = 420$$

```lean
-- SUCCESS의 재배열 수
example : Nat.factorial 7 / (Nat.factorial 3 * Nat.factorial 1 *
          Nat.factorial 2 * Nat.factorial 1) = 420 := by native_decide
```

### 9F.2.4 다항 계수를 이항 계수로 표현하기

다항 계수는 이항 계수의 곱으로도 표현할 수 있다:

$$\frac{n!}{n_1! \cdot n_2! \cdot \cdots \cdot n_k!} = \binom{n}{n_1} \binom{n-n_1}{n_2} \binom{n-n_1-n_2}{n_3} \cdots$$

```lean
-- SUCCESS를 이항 계수의 곱으로 계산
-- = C(7,3) × C(4,1) × C(3,2) × C(1,1)
-- 먼저 S 3개의 위치 선택: C(7, 3) = 35
-- 그 다음 U 1개의 위치 선택: C(4, 1) = 4
-- 그 다음 C 2개의 위치 선택: C(3, 2) = 3
-- 마지막 E 1개의 위치: C(1, 1) = 1
example : Nat.choose 7 3 * Nat.choose 4 1 * Nat.choose 3 2 * Nat.choose 1 1 = 420 := by
  native_decide
```

---

## 9F.3 **중복 조합**(Combinations with Repetition)

### 9F.3.1 기본 아이디어

**중복 조합**: n종류의 원소에서 **반복을 허용하여** r개를 **순서 없이** 선택하는 방법의 수.

예: 도넛 가게에 초콜릿, 글레이즈, 시나몬 3종류가 있고, 6개를 선택한다고 하자 (같은 종류를 여러 개 선택 가능). 이 경우의 수는?

> **정리**: n종류의 원소에서 반복을 허용하여 r개를 선택하는 방법의 수는  
> $$C(n + r - 1, r) = \binom{n + r - 1}{r}$$

### 9F.3.2 **별과 막대**(Stars and Bars) 기법

이 공식을 이해하는 가장 좋은 방법은 **별과 막대**(stars and bars) 기법이다.

r개의 "별"(★)을 n개의 종류로 나누려면 n-1개의 "막대"(|)가 필요하다. 총 r + (n-1)개의 위치 중에서 n-1개의 막대 위치를 선택하면 된다.

**예**: 3종류 도넛에서 6개 선택 → 6개의 별과 2개의 막대

- ★★|★★★|★ → 초콜릿 2개, 글레이즈 3개, 시나몬 1개
- |★★★★★★| → 초콜릿 0개, 글레이즈 6개, 시나몬 0개
- ★★★★★★|| → 초콜릿 6개, 글레이즈 0개, 시나몬 0개

총 r + n - 1 = 6 + 3 - 1 = 8개의 위치에서 막대(또는 별)의 위치를 고르면 된다:

$$C(8, 2) = C(8, 6) = 28$$

```lean
-- 3종류 도넛에서 6개 선택
-- C(3 + 6 - 1, 6) = C(8, 6) = 28
example : Nat.choose 8 6 = 28 := by native_decide

-- 또는 C(8, 2) = 28
example : Nat.choose 8 2 = 28 := by native_decide
```

### 9F.3.3 Lean 4에서 중복 조합

```lean
import Mathlib

-- 중복 조합 공식: C(n + r - 1, r)

-- 4종류에서 3개 선택 (반복 허용)
-- C(4 + 3 - 1, 3) = C(6, 3) = 20
example : Nat.choose 6 3 = 20 := by native_decide

-- 5종류에서 4개 선택 (반복 허용)
-- C(5 + 4 - 1, 4) = C(8, 4) = 70
example : Nat.choose 8 4 = 70 := by native_decide
```

---

## 9F.4 요약: 네 가지 유형의 비교

| 유형 | 순서 | 반복 | 공식 | Lean 4 |
|------|------|------|------|--------|
| **순열** | 있음 | 없음 | P(n,r) = n!/(n-r)! | `Nat.descFactorial n r` |
| **반복 허용 순열** | 있음 | 있음 | nʳ | `Fintype.card (Fin r → Fin n)` |
| **조합** | 없음 | 없음 | C(n,r) = n!/(r!(n-r)!) | `Nat.choose n r` |
| **중복 조합** | 없음 | 있음 | C(n+r-1, r) | `Nat.choose (n+r-1) r` |

이 표는 매우 중요하다! 어떤 계수 문제를 만나면 먼저 "순서가 중요한가?"와 "반복이 허용되는가?"를 판단하면 된다.

---

## 9F.5 종합 연습문제

### 🏋️ 연습 9F-1: 반복 허용 순열 (괄호 채우기)

```lean
-- 10진 숫자(0~9)로 이루어진 길이 4인 비밀번호의 수
example : 10^4 = ⟨___⟩ := by norm_num

-- 이진 문자열(0, 1) 길이 8의 수
example : 2^8 = ⟨___⟩ := by norm_num

-- 알파벳 소문자 26개로 만든 길이 3 문자열의 수
example : 26^3 = ⟨___⟩ := by norm_num
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : 10^4 = 10000 := by norm_num
example : 2^8 = 256 := by norm_num
example : 26^3 = 17576 := by norm_num
```

</details>

### 🏋️ 연습 9F-2: 구별할 수 없는 원소의 순열 (괄호 채우기)

```lean
-- 'MISSISSIPPI'의 재배열 수 (M:1, I:4, S:4, P:2, 총 11자)
-- 11! / (1! × 4! × 4! × 2!) = ?
example : Nat.factorial 11 / (Nat.factorial 1 * Nat.factorial 4 *
          Nat.factorial 4 * Nat.factorial 2) = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.factorial 11 / (Nat.factorial 1 * Nat.factorial 4 *
          Nat.factorial 4 * Nat.factorial 2) = 34650 := by native_decide
```

**해설**: 11! = 39916800, 1! × 4! × 4! × 2! = 1 × 24 × 24 × 2 = 1152, 39916800 / 1152 = 34650이다.

</details>

### 🏋️ 연습 9F-3: 중복 조합 — 별과 막대 (괄호 채우기)

```lean
-- 아이스크림 가게에 5가지 맛이 있다. 3 scoops를 고르는 방법은?
-- (같은 맛 중복 가능, 순서 무관)
-- C(5 + 3 - 1, 3) = C(7, 3) = ?
example : Nat.choose 7 3 = ⟨___⟩ := by native_decide

-- 4종류의 과일에서 10개를 사는 방법은? (중복 허용)
-- C(4 + 10 - 1, 10) = C(13, 10) = ?
example : Nat.choose 13 10 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 7 3 = 35 := by native_decide
example : Nat.choose 13 10 = 286 := by native_decide
```

**해설**: 
- 5가지 맛, 3 scoops: C(5+3-1, 3) = C(7, 3) = 35
- 4종류 과일, 10개: C(4+10-1, 10) = C(13, 10) = C(13, 3) = 286

</details>

### 🏋️ 연습 9F-4: 유형 판별 종합 (sorry 방식)

```lean
-- 다음 각 상황이 네 가지 유형 중 어떤 것인지 판단하고 계산하라

-- (1) 7명을 일렬로 세우는 방법 → 순열 (반복 없음)
example : Nat.factorial 7 = 5040 := by sorry

-- (2) 16진수(0~9, A~F)로 길이 6인 주소를 만드는 방법 → 반복 허용 순열
example : 16^6 = 16777216 := by sorry

-- (3) 20명 중 5명을 뽑아 위원회를 구성하는 방법 → 조합 (반복 없음)
example : Nat.choose 20 5 = 15504 := by sorry

-- (4) 6종류 음료에서 4잔을 주문하는 방법 (같은 음료 가능) → 중복 조합
-- C(6+4-1, 4) = C(9, 4)
example : Nat.choose 9 4 = 126 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.factorial 7 = 5040 := by native_decide
example : 16^6 = 16777216 := by norm_num
example : Nat.choose 20 5 = 15504 := by native_decide
example : Nat.choose 9 4 = 126 := by native_decide
```

**해설**: 핵심은 "순서가 중요한가?"와 "반복이 가능한가?"를 먼저 판단하는 것이다.

| 문제 | 순서 | 반복 | 유형 | 공식 |
|------|------|------|------|------|
| (1) 7명 줄 세우기 | ○ | × | 순열 | 7! = 5040 |
| (2) 16진수 주소 | ○ | ○ | 반복 순열 | 16⁶ |
| (3) 위원회 구성 | × | × | 조합 | C(20, 5) |
| (4) 음료 주문 | × | ○ | 중복 조합 | C(9, 4) |

</details>

### 🏋️ 연습 9F-5: ABRACADABRA 재배열 (sorry 방식)

```lean
-- 'ABRACADABRA'의 재배열 수 (A:5, B:2, R:2, C:1, D:1, 총 11자)
-- 11! / (5! × 2! × 2! × 1! × 1!)
example : Nat.factorial 11 / (Nat.factorial 5 * Nat.factorial 2 *
          Nat.factorial 2 * Nat.factorial 1 * Nat.factorial 1) = 83160 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.factorial 11 / (Nat.factorial 5 * Nat.factorial 2 *
          Nat.factorial 2 * Nat.factorial 1 * Nat.factorial 1) = 83160 := by native_decide
```

**해설**: 11! = 39916800, 5! × 2! × 2! × 1! × 1! = 120 × 2 × 2 × 1 × 1 = 480, 39916800 / 480 = 83160이다.

</details>

### 🏋️ 연습 9F-6: 방정식의 해의 수 (sorry 방식)

```lean
-- x₁ + x₂ + x₃ + x₄ = 10 (xᵢ ≥ 0인 정수)의 해의 수는?
-- 이것은 4종류에서 10개를 중복 선택하는 것과 같다
-- C(4 + 10 - 1, 10) = C(13, 10) = C(13, 3)
example : Nat.choose 13 10 = Nat.choose 13 3 := by sorry
example : Nat.choose 13 3 = 286 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 13 10 = Nat.choose 13 3 := by native_decide
example : Nat.choose 13 3 = 286 := by native_decide
```

**해설**: x₁ + x₂ + ··· + xₖ = n (xᵢ ≥ 0)의 음이 아닌 정수 해의 수는 **별과 막대** 기법으로 C(k + n - 1, n)이다. 여기서 k = 4, n = 10이므로 C(13, 10) = C(13, 3) = 286이다.

</details>

### 🏋️ 연습 9F-7: Fin 타입과 반복 허용 순열 (sorry 방식)

```lean
import Mathlib

-- Fin r → Fin n의 원소 수가 n^r임을 확인하라
example : Fintype.card (Fin 3 → Fin 4) = 64 := by sorry
-- (4³ = 64: 4종류에서 반복 허용하여 3개 나열)

example : Fintype.card (Fin 5 → Fin 2) = 32 := by sorry
-- (2⁵ = 32: 길이 5인 이진 문자열의 수)
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Fintype.card (Fin 3 → Fin 4) = 64 := by simp
example : Fintype.card (Fin 5 → Fin 2) = 32 := by simp
```

**해설**: `Fintype.card (Fin r → Fin n)`은 `simp`가 자동으로 `n^r`으로 계산해준다. Fin 3 → Fin 4는 4³ = 64이고, Fin 5 → Fin 2는 2⁵ = 32이다.

</details>

---

## 9F.6 이 장의 핵심 요약

### 네 가지 계수 유형 총정리

```
                   반복 없음            반복 허용
              ┌─────────────────┬──────────────────┐
  순서 있음    │  P(n,r)          │  n^r              │
  (순열)      │  = n!/(n-r)!     │                   │
              ├─────────────────┼──────────────────┤
  순서 없음    │  C(n,r)          │  C(n+r-1, r)      │
  (조합)      │  = n!/(r!(n-r)!) │  = (n+r-1)!       │
              │                 │    /(r!(n-1)!)     │
              └─────────────────┴──────────────────┘
```

### 추가 개념

| 개념 | 공식 | 예시 |
|------|------|------|
| **구별 불가 원소의 순열** | n! / (n₁!·n₂!·····nₖ!) | 'SUCCESS' = 420 |
| **별과 막대** 기법 | x₁+···+xₖ=n의 해 = C(k+n-1, n) | 도넛 선택 |

### 주요 Lean 4 도구 (추가)

| 함수/전술 | 용도 |
|---------|------|
| `Fintype.card (Fin r → Fin n)` | 반복 허용 순열 = nʳ |
| `Nat.factorial n / (Nat.factorial n₁ * ...)` | 다항 계수 |
| `norm_num` | 거듭제곱 등 산술 계산 |
| `simp` | Fintype.card 자동 계산 |

---

> **Part 9 시리즈 완결!** Part 9-A~F를 통해 Rosen 이산수학 6장(계수) 전체를 Lean 4와 함께 학습했다. 다음 주제로 넘어갈 준비가 되었다!
