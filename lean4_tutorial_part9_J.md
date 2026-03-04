# Lean4 완전 정복 가이드 —  Part 9-J: 일반화된 순열과 조합 — Lean 4 형식화 연습

> **Rosen 이산수학 8판 §6.5~6.6 기반 · Mathematics in Lean Chapter 6 연결**
> 이전 파트(Part 9-I)에서 `rw`, `intro`, `apply`, `calc`, `↔` 등의 기초 도구를 배웠다.
> 이번 파트에서는 이 도구들을 사용하여 Rosen 6.5~6.6절의 문제를 Lean 4로 풀어본다.

---

##  이 파트에서 다루는 내용

| 순서 | 주제 | Rosen 절 |
|------|------|---------|
| 9J.1 | **반복 허용 순열**(permutation with repetition): nʳ | §6.5.2 |
| 9J.2 | **반복 허용 조합**(combination with repetition): C(n+r-1, r) | §6.5.3 |
| 9J.3 | **구별 불가 객체의 순열**: 다항 계수 n!/(n₁!⋯nₖ!) | §6.5.4 |
| 9J.4 | **객체를 상자에 분배하기**: 4가지 유형 | §6.5.5 |
| 9J.5 | **순열과 조합의 생성** | §6.6 |
| 9J.6 | 종합 연습문제 | §6.5~6.6 연습문제 |

---

## 9J.0 준비 — Lean 4에서 계수를 위한 도구들

이 파트에서 사용할 핵심 Lean 4 라이브러리를 먼저 소개한다.

```lean
import Mathlib.Data.Nat.Choose.Basic      -- Nat.choose (이항 계수 C(n,r))
import Mathlib.Data.Nat.Factorial.Basic   -- Nat.factorial (n!)
import Mathlib.Data.Fintype.Card          -- Fintype.card (타입의 원소 수)
import Mathlib.Data.Fin.Basic             -- Fin n (0부터 n-1까지의 타입)

open Nat Fintype Finset
```

### 핵심 함수/정리 정리

| Lean 4 표현 | 수학 의미 | 예시 |
|-------------|---------|------|
| `Nat.factorial n` | n! | `factorial 5 = 120` |
| `Nat.choose n r` | C(n, r) | `choose 5 3 = 10` |
| `card (Fin n)` | n개의 원소 | `card (Fin 5) = 5` |
| `card (Fin n → Fin m)` | mⁿ (함수의 수) | 반복 허용 순열 |
| `card (Fin n × Fin m)` | n × m | 곱셈 법칙 |
| `(card α) ^ n` | (원소 수)ⁿ | 거듭제곱 |

---

## 9J.1 반복 허용 순열 — nʳ

### 📖 이론 복습

**반복을 허용하는 순열**(permutation with repetition)이란:
- n개의 원소를 가진 집합에서
- **같은 원소를 여러 번** 선택할 수 있게 하면서
- r개를 **순서대로** 나열하는 것

예를 들어, 26개의 영어 대문자로 길이 3인 문자열을 만드는 경우의 수는?
→ 각 위치에서 26가지 선택이 가능하므로 26³ = 17,576가지.

> **정리**(Theorem): 반복이 허용될 때, n개의 원소를 갖는 집합에서 r-순열의 개수는 **nʳ**이다.

### 🖥️ Lean 4 형식화

Lean 4에서 "n개 원소에서 r개를 순서대로 고르되 반복 허용"은
`Fin r → Fin n` 타입의 **함수**로 표현한다.

왜 함수인가? 각 위치(1번째, 2번째, ..., r번째)에 대해 어떤 원소를 배치할지 결정하는 것이
곧 함수 `위치 → 원소`이기 때문이다.

```lean
-- Lean은 Fin r → Fin n 타입의 원소 수가 n^r 임을 안다
example (n r : Nat) : card (Fin r → Fin n) = n ^ r := by
  simp
```

### 📝 예제 1 (Rosen 예제 1): 영어 대문자 문자열

> 영어 대문자 알파벳으로 이루어진 길이 r의 문자열은 모두 몇 가지인가?

```lean
-- 26개 대문자로 길이 r인 문자열의 수 = 26^r
example (r : Nat) : card (Fin r → Fin 26) = 26 ^ r := by
  simp
```

**설명**: `Fin r`은 문자열의 각 위치(0, 1, ..., r-1)를 나타내고,
`Fin 26`은 26개의 대문자(A~Z)를 나타낸다.
함수 `Fin r → Fin 26`은 "각 위치에 어떤 문자를 넣을지"를 결정한다.

### 📝 구체적 계산: r = 3일 때

```lean
-- 길이 3인 대문자 문자열의 수 = 26³ = 17576
example : card (Fin 3 → Fin 26) = 17576 := by
  simp
  norm_num
```

### ✏️ 연습 9J.1-a: 비밀번호 (괄호 채우기)

> 숫자 0~9로 이루어진 길이 4인 비밀번호의 수를 구하라.

```lean
example : card (Fin 4 → Fin 10) = /-[ 여기를 채우세요 ]-/ := by
  simp
  norm_num
```

<details>
<summary>✅ 답 보기</summary>

```lean
-- 10⁴ = 10000
example : card (Fin 4 → Fin 10) = 10000 := by
  simp
  norm_num
```

4자리 비밀번호는 각 자리에 10가지 선택 → 10⁴ = 10,000가지.

</details>

### ✏️ 연습 9J.1-b: 이진 문자열 (sorry)

> 길이 8인 비트 문자열(0과 1로 구성)의 수를 구하라.

```lean
example : card (Fin 8 → Fin 2) = 256 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : card (Fin 8 → Fin 2) = 256 := by
  simp
  norm_num
  -- 2⁸ = 256
```

</details>

### ✏️ 연습 9J.1-c: 일반적인 공식 (sorry)

> n^r 공식을 직접 증명하라.

```lean
-- 이것이 반복 허용 순열의 핵심 정리이다
theorem perm_with_rep (n r : Nat) : card (Fin r → Fin n) = n ^ r := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
theorem perm_with_rep (n r : Nat) : card (Fin r → Fin n) = n ^ r := by
  simp
```

`simp`는 `Fintype.card_fun`, `Fintype.card_fin` 등의 보조정리를 자동 적용한다.

</details>

---

## 9J.2 반복 허용 조합 — C(n+r-1, r)

### 📖 이론 복습

**반복을 허용하는 조합**(combination with repetition)이란:
- n개의 **종류**가 있는 집합에서
- **같은 종류를 여러 번** 선택할 수 있고
- **순서는 무시**하면서
- r개를 선택하는 것

> **정리**(Theorem): 원소의 중복을 허락할 경우 n개의 원소의 집합으로부터 가능한 r-조합의 수는
> **C(n + r - 1, r)** 또는 동일하게 **C(n + r - 1, n - 1)**이다.

### 🌟 별과 막대 기법 (Stars and Bars)

이 공식의 핵심 아이디어는 **별과 막대**(stars and bars) 기법이다.

r개의 별(★)과 (n-1)개의 막대(|)를 일렬로 나열하는 경우의 수와 같다!

예: 3종류(사과, 귤, 배)에서 4개 선택
- ★★|★|★ → 사과 2, 귤 1, 배 1
- |★★★|★ → 사과 0, 귤 3, 배 1
- ★★★★|| → 사과 4, 귤 0, 배 0

총 나열할 것: r개의 ★ + (n-1)개의 | = (n+r-1)개
이 중 ★의 위치(r개)를 고르면 됨 → **C(n+r-1, r)**

### 🖥️ Lean 4에서의 표현

```lean
-- 반복 허용 조합의 수 = C(n + r - 1, r)
-- Lean에서 Nat 뺄셈은 0에서 멈추므로 조심해야 한다!
-- n ≥ 1일 때 (즉 원소가 하나 이상일 때):

example : Nat.choose (3 + 4 - 1) 4 = 15 := by
  -- C(6, 4) = C(6, 2) = 15
  native_decide
```

### 📝 예제 2 (Rosen 예제 2): 과일 선택

> 사과, 귤, 배가 담겨있는 바구니에서 4개의 과일을 선택하는 경우의 수는?
> (순서 무시, 같은 종류 반복 가능)

```lean
-- n = 3 (사과, 귤, 배), r = 4
-- C(3 + 4 - 1, 4) = C(6, 4) = 15
example : Nat.choose 6 4 = 15 := by native_decide
```

### 📝 예제 3 (Rosen 예제 3): 지폐 선택

> 7종류의 지폐(1, 2, 5, 10, 20, 50, 100달러)에서 5장을 선택하는 방법의 수는?

```lean
-- n = 7, r = 5
-- C(7 + 5 - 1, 5) = C(11, 5) = 462
example : Nat.choose 11 5 = 462 := by native_decide
```

### 📝 예제 5 (Rosen 예제 5): 방정식의 해의 수

> x₁ + x₂ + x₃ = 11의 음이 아닌 정수 해는 몇 개인가?

이것은 "3개 원소의 집합에서 중복을 허용하여 11개를 선택"하는 것과 같다!
- x₁ = 첫 번째 원소를 고른 횟수
- x₂ = 두 번째 원소를 고른 횟수
- x₃ = 세 번째 원소를 고른 횟수

```lean
-- n = 3, r = 11
-- C(3 + 11 - 1, 11) = C(13, 11) = C(13, 2) = 78
example : Nat.choose 13 11 = 78 := by native_decide

-- C(13, 2)로 계산해도 같다 (대칭성)
example : Nat.choose 13 2 = 78 := by native_decide
```

### ✏️ 연습 9J.2-a: 과자 가게 (괄호 채우기)

> 과자 가게에서 4가지 종류의 과자를 판다. 6개의 과자를 선택하는 방법은?
> (Rosen 예제 4)

```lean
-- n = 4, r = 6
-- C(4 + 6 - 1, 6) = C(9, 6) = ?
example : Nat.choose 9 6 = /-[ 여기를 채우세요 ]-/ := by native_decide
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 9 6 = 84 := by native_decide
-- C(9, 6) = C(9, 3) = 9·8·7 / (1·2·3) = 84
```

</details>

### ✏️ 연습 9J.2-b: 방정식의 해 (sorry)

> x₁ + x₂ + x₃ + x₄ = 17의 음이 아닌 정수 해의 수를 구하라.

```lean
-- n = 4 (변수의 수), r = 17 (합)
-- C(4 + 17 - 1, 17) = C(20, 17) = C(20, 3)
example : Nat.choose 20 17 = 1140 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 20 17 = 1140 := by native_decide
-- C(20, 3) = 20·19·18 / (1·2·3) = 1140
```

</details>

### ✏️ 연습 9J.2-c: 제한 있는 방정식 (Rosen 연습문제 유형)

> x₁ + x₂ + x₃ = 11, 단 x₁ ≥ 1, x₂ ≥ 2, x₃ ≥ 3 일 때 해의 수는?

**아이디어**: y₁ = x₁ - 1, y₂ = x₂ - 2, y₃ = x₃ - 3으로 치환하면
y₁ + y₂ + y₃ = 11 - 1 - 2 - 3 = 5, y₁, y₂, y₃ ≥ 0

```lean
-- n = 3, r = 5
-- C(3 + 5 - 1, 5) = C(7, 5) = C(7, 2)
example : Nat.choose 7 5 = 21 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 7 5 = 21 := by native_decide
-- C(7, 2) = 7·6 / (1·2) = 21
```

</details>

---

## 9J.3 구별 불가 객체의 순열 — 다항 계수

### 📖 이론 복습

n개의 객체 중에서 구별할 수 없는 유형 1의 객체가 n₁개, 유형 2의 객체가 n₂개, ...,
유형 k의 객체가 nₖ개 있을 때, 서로 다른 순열의 수는:

> **n! / (n₁! · n₂! · ⋯ · nₖ!)**

### 📝 예제 7 (Rosen): "SUCCESS"의 재배치

> "SUCCESS" 단어의 문자들을 재배치하여 만들 수 있는 문자열은?
> S: 3개, U: 1개, C: 2개, E: 1개 → 총 7개

```lean
-- 7! / (3! · 2! · 1! · 1!) = 5040 / 12 = 420
example : 5040 / (6 * 2 * 1 * 1) = 420 := by norm_num

-- 각 팩토리얼 확인
example : Nat.factorial 7 = 5040 := by native_decide
example : Nat.factorial 3 = 6 := by native_decide
example : Nat.factorial 2 = 2 := by native_decide
```

### 📝 예제 8 (Rosen): 카드 분배

> 52장의 카드에서 4명의 경기자에게 각각 5장의 카드를 분배하는 서로 다른 방법의 수는?

```lean
-- C(52,5) · C(47,5) · C(42,5) · C(37,5) = 52! / (5!·5!·5!·5!·32!)
-- 개별 계산
example : Nat.choose 52 5 = 2598960 := by native_decide
example : Nat.choose 47 5 = 1533939 := by native_decide
example : Nat.choose 42 5 = 850668 := by native_decide
example : Nat.choose 37 5 = 435897 := by native_decide
```

### ✏️ 연습 9J.3-a: MISSISSIPPI (sorry)

> "MISSISSIPPI"의 문자를 재배치하는 방법의 수는?
> M: 1, I: 4, S: 4, P: 2 → 총 11

```lean
-- 11! / (1! · 4! · 4! · 2!)
example : Nat.factorial 11 = 39916800 := by native_decide
-- 분모: 1 · 24 · 24 · 2 = 1152
-- 39916800 / 1152 = 34650
example : 39916800 / 1152 = 34650 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : 39916800 / 1152 = 34650 := by norm_num
```

</details>

### ✏️ 연습 9J.3-b: ABRACADABRA (sorry)

> "ABRACADABRA"의 문자를 재배치하는 방법의 수는?
> A: 5, B: 2, R: 2, C: 1, D: 1 → 총 11

```lean
-- 11! / (5! · 2! · 2! · 1! · 1!)
-- = 39916800 / (120 · 2 · 2 · 1 · 1)
-- = 39916800 / 480 = 83160
example : 39916800 / 480 = 83160 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : 39916800 / 480 = 83160 := by norm_num
```

</details>

---

## 9J.4 객체를 상자에 분배하기 — 4가지 유형

### 📖 이론 복습: 4가지 유형 비교표

많은 계수 문제는 **객체**(objects)를 **상자**(boxes)에 넣는 것으로 볼 수 있다.
객체와 상자의 **구별 가능 여부**에 따라 4가지 유형이 있다:

| 유형 | 객체 | 상자 | 공식 | 비유 |
|------|------|------|------|------|
| ① | **구별 가능** | **구별 가능** | 다항 계수 n!/(n₁!⋯nₖ!) | 학생을 반에 배치 |
| ② | **구별 불가** | **구별 가능** | C(n+k-1, n) | 동전을 저금통에 분배 |
| ③ | **구별 가능** | **구별 불가** | 스털링 수 S(n,k) | 사무실 배치 |
| ④ | **구별 불가** | **구별 불가** | 자연수 분할 p(n) | 책을 상자에 포장 |

### 🖥️ Lean 4에서의 유형 ①: 구별 가능 → 구별 가능

```lean
-- n개의 구별 가능 객체를 k개의 구별 가능 상자에 넣기 = kⁿ
-- (각 객체마다 k개 상자 중 하나를 선택)
-- 이것은 함수 Fin n → Fin k 의 수와 같다!

example : card (Fin 3 → Fin 4) = 64 := by
  simp; norm_num
  -- 4³ = 64
```

### 🖥️ Lean 4에서의 유형 ②: 구별 불가 → 구별 가능

```lean
-- 10개의 구별 불가 공을 8개의 구별 가능 상자에 넣기
-- = C(8 + 10 - 1, 10) = C(17, 10)
-- (Rosen 예제 9)

example : Nat.choose 17 10 = 19448 := by native_decide
```

### 📝 예제 9 (Rosen): 구별 불가 공 → 구별 가능 상자

> 8개의 구별 가능한 구명에 10개의 구별되지 않는 공들을 넣는 가능한 방법은?

```lean
-- C(8 + 10 - 1, 10) = C(17, 10) = 19,448
example : Nat.choose 17 10 = 19448 := by native_decide
```

### ✏️ 연습 9J.4-a: 학생 배치 (괄호 채우기)

> 5명의 서로 다른 학생을 3개의 서로 다른 조에 배치하는 방법의 수는?

```lean
-- 유형 ①: 3⁵ = ?
example : card (Fin 5 → Fin 3) = /-[ 여기를 채우세요 ]-/ := by
  simp; norm_num
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : card (Fin 5 → Fin 3) = 243 := by
  simp; norm_num
  -- 3⁵ = 243
```

</details>

### ✏️ 연습 9J.4-b: 동전 분배 (sorry)

> 20개의 동일한 동전을 4개의 서로 다른 저금통에 넣는 방법의 수는?

```lean
-- 유형 ②: C(4 + 20 - 1, 20) = C(23, 20) = C(23, 3)
example : Nat.choose 23 20 = 1771 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 23 20 = 1771 := by native_decide
-- C(23, 3) = 23·22·21 / (1·2·3) = 1771
```

</details>

### ✏️ 연습 9J.4-c: 동전 선택 (Rosen 연습 12)

> 저금통에 20개의 동전(1원, 10원, 50원, 100원, 500원짜리)이 있다.
> 8개의 동전을 선택하는 서로 다른 조합의 수는?

```lean
-- n = 5 (동전 종류), r = 8 (선택 수)
-- C(5 + 8 - 1, 8) = C(12, 8) = C(12, 4)
example : Nat.choose 12 8 = 495 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 12 8 = 495 := by native_decide
-- C(12, 4) = 12·11·10·9 / (1·2·3·4) = 495
```

</details>

---

## 9J.5 순열과 조합의 생성 (§6.6)

### 📖 이론 복습: 사전순 정렬

**사전순 정렬**(lexicographic ordering)은 사전에서 단어를 찾는 순서와 같다.
두 순열을 비교할 때, 왼쪽부터 하나씩 비교하여 처음 다른 위치에서 작은 쪽이 앞에 온다.

### 📝 예제 (Rosen 예제 1): 사전순 비교

> {1, 2, 3, 4, 5}에 대한 순열 23415는 순열 23514보다 앞에 나온다.
> 세 번째 위치의 숫자가 첫 번째 순열은 4이고 두 번째 순열은 5로서 첫 번째 순열의 수가 작기 때문이다.

```lean
-- 리스트의 사전순 비교
example : [2,3,4,1,5] < [2,3,5,1,4] := by decide
```

### 🖥️ Lean 4에서 순열 다루기

Lean의 Mathlib에서 순열은 `Equiv.Perm (Fin n)` 타입으로 표현된다.
하지만 여기서는 더 직관적인 **리스트**로 작업한다.

```lean
-- 리스트 비교 (사전순)
#eval ([1,2,3] : List Nat) < [1,2,4]   -- true
#eval ([1,2,3] : List Nat) < [1,3,2]   -- true
#eval ([2,1,3] : List Nat) < [1,2,3]   -- false (2 > 1)
```

### 🔄 다음 순열 알고리즘 (Rosen 알고리즘 1)

Rosen의 알고리즘을 Lean 4 스타일로 설명하면:

**입력**: 순열 a₁a₂...aₙ (마지막 순열이 아닌 것)

1. **오른쪽에서 감소하지 않는 가장 큰 j를 찾기**: aⱼ < aⱼ₊₁인 가장 큰 j
2. **aⱼ보다 큰 가장 오른쪽의 aₖ를 찾기**
3. **aⱼ와 aₖ를 교환**
4. **j+1번째부터 끝까지를 뒤집기** (오름차순으로 만들기)

### 📝 예제 (Rosen 예제 2): 362541 → 다음 순열

> 362541의 다음으로 큰 순열은?

단계별:
1. 오른쪽에서 보면 5 > 4 > 1이고, 2 < 5이므로 j = 3 (aⱼ = 2)
2. 2보다 크고 가장 오른쪽인 것: aₖ = 4
3. 교환: 3 6 **4** 5 **2** 1 → 364521 (아직 미완성)
4. j+1=4번째부터 뒤집기: 364**125**

결과: **364125**

```lean
-- 확인: 364125 > 362541 (사전순)
example : [3,6,4,1,2,5] > [3,6,2,5,4,1] := by decide
```

### ✏️ 연습 9J.5-a: 다음 순열 찾기 (개념 확인)

> 12453의 다음 순열을 직접 구한 후, Lean으로 순서를 확인하라.

```lean
-- 12453의 다음 순열은?
-- j = 3 (a₃ = 4 < a₄ = 5), k = 4 (a₄ = 5)
-- 교환: 12543 → 뒤집기: 12534? 아니...
-- 다시: j = 3이면 a₃ = 4, a₄ = 5, a₅ = 3
-- a_j = 4 < a_{j+1} = 5, j = 3
-- k: 4보다 큰 가장 오른쪽 = 5 (위치 4)
-- 교환: 1,2,5,4,3 → j+1=4부터 뒤집기: 1,2,5,3,4

-- 정답: 12534
example : [1,2,5,3,4] > [1,2,4,5,3] := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : [1,2,5,3,4] > [1,2,4,5,3] := by decide
```

</details>

### ✏️ 연습 9J.5-b: 비트 문자열 (Rosen 예제 4)

> 10 0010 0111 다음으로 큰 비트 문자열을 찾아라.

**알고리즘**: 오른쪽에서 첫 번째 0을 찾아 1로 바꾸고, 그 다음의 1을 모두 0으로 바꾼다.

```lean
-- 10 0010 0111의 다음 = 10 0010 1000
-- (오른쪽에서 4번째가 첫 번째 0, 이를 1로 바꾸고 나머지 0)
example : [1,0,0,0,1,0,1,0,0,0] > [1,0,0,0,1,0,0,1,1,1] := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : [1,0,0,0,1,0,1,0,0,0] > [1,0,0,0,1,0,0,1,1,1] := by decide
```

</details>

---

## 9J.6 종합 연습문제

### ✏️ 연습 9J.6-a: 반복 허용 순열 — 6자리 (sorry)

> 6자의 영문자로 이루어진 단어는 모두 몇 개인가? (Rosen 연습 3)

```lean
-- 26⁶
example : card (Fin 6 → Fin 26) = 308915776 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : card (Fin 6 → Fin 26) = 308915776 := by
  simp; norm_num
```

</details>

### ✏️ 연습 9J.6-b: 샌드위치 선택 (Rosen 연습 4)

> 6종류의 샌드위치 중 매일 포장된 샌드위치를 선택, 7일간 서로 다른 방법은?
> (반복 허용 순열: 순서 중요, 같은 종류 반복 가능)

```lean
-- 6⁷
example : card (Fin 7 → Fin 6) = 279936 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : card (Fin 7 → Fin 6) = 279936 := by
  simp; norm_num
```

</details>

### ✏️ 연습 9J.6-c: 도너츠 선택 (Rosen 연습 8)

> 도너츠 가게에서 21종류의 도너츠 중 12개를 선택, 서로 다른 방법의 수는?
> (반복 허용 조합: 순서 무관, 같은 종류 반복 가능)

```lean
-- C(21 + 12 - 1, 12) = C(32, 12)
example : Nat.choose 32 12 = 225792840 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 32 12 = 225792840 := by native_decide
```

</details>

### ✏️ 연습 9J.6-d: 작업 할당 (Rosen 연습 5)

> 3가지의 작업을 5명의 사원에게 할당한다. 각 사원에게 한 가지 이상의 작업을
> 할당할 수도 있다면, 할당하는 방법은 모두 몇 가지인가?

```lean
-- 각 작업에 대해 5명 중 1명 선택 = 5³
example : card (Fin 3 → Fin 5) = 125 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : card (Fin 3 → Fin 5) = 125 := by
  simp; norm_num
```

</details>

### ✏️ 연습 9J.6-e: 중복 조합 — 순서 무관 (Rosen 연습 6)

> 원소가 3개인 집합에서 중복을 허용하여 5개의 원소를 순서에 관계없이 선택하는 수는?

```lean
-- C(3 + 5 - 1, 5) = C(7, 5) = C(7, 2) = 21
example : Nat.choose 7 5 = 21 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 7 5 = 21 := by native_decide
```

</details>

### ✏️ 연습 9J.6-f: 중복 조합 — 5개 원소에서 3개 (Rosen 연습 7)

> 원소가 5개인 집합에서 중복을 허용하여 3개의 원소를 순서에 관계없이 선택하는 수는?

```lean
-- C(5 + 3 - 1, 3) = C(7, 3)
example : Nat.choose 7 3 = 35 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 7 3 = 35 := by native_decide
```

</details>

### ✏️ 연습 9J.6-g: 방정식의 해 — 하한 있음 (Rosen 연습 15a)

> x₁ + x₂ + x₃ + x₄ + x₅ = 21, 모든 변수가 음이 아닌 정수일 때, 해의 수는?
> 단 x₁ ≥ 1.

```lean
-- y₁ = x₁ - 1로 치환하면 y₁ + x₂ + x₃ + x₄ + x₅ = 20
-- n = 5, r = 20
-- C(5 + 20 - 1, 20) = C(24, 20) = C(24, 4)
example : Nat.choose 24 4 = 10626 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 24 4 = 10626 := by native_decide
```

</details>

### ✏️ 연습 9J.6-h: 구별 불가 객체 분배 (Rosen 연습 23)

> 동일한 6개의 공을 서로 다른 9개의 상자에 분배하는 방법은?

```lean
-- C(9 + 6 - 1, 6) = C(14, 6)
example : Nat.choose 14 6 = 3003 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 14 6 = 3003 := by native_decide
```

</details>

### ✏️ 연습 9J.6-i: 이항 계수 대칭성 (→ 와 ↔ 활용)

```lean
-- C(n, r) = C(n, n-r) 의 구체적 예를 증명하라
-- 이것은 ↔가 아닌 = (동치가 아닌 등식)이다

-- 방법 1: 구체적 수치 확인
example : Nat.choose 10 3 = Nat.choose 10 7 := by
  sorry

-- 방법 2: 일반적 정리 사용
-- Nat.choose_symm : n.choose r = n.choose (n - r)
example (n r : Nat) (h : r ≤ n) : Nat.choose n r = Nat.choose n (n - r) := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example : Nat.choose 10 3 = Nat.choose 10 7 := by native_decide

example (n r : Nat) (h : r ≤ n) : Nat.choose n r = Nat.choose n (n - r) := by
  exact Nat.choose_symm h
```

</details>

### ✏️ 연습 9J.6-j: lemma + theorem 구조 (종합)

```lean
-- 보조정리: C(n, 0) = 1
lemma choose_zero (n : Nat) : Nat.choose n 0 = 1 := by
  sorry

-- 보조정리: C(n, n) = 1
lemma choose_self (n : Nat) : Nat.choose n n = 1 := by
  sorry

-- 정리: C(n, 0) + C(n, n) = 2
theorem choose_ends (n : Nat) : Nat.choose n 0 + Nat.choose n n = 2 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
lemma choose_zero (n : Nat) : Nat.choose n 0 = 1 := by
  simp [Nat.choose_zero_right]

lemma choose_self (n : Nat) : Nat.choose n n = 1 := by
  simp [Nat.choose_self]

theorem choose_ends (n : Nat) : Nat.choose n 0 + Nat.choose n n = 2 := by
  rw [choose_zero, choose_self]   -- 보조정리 사용!
```

이것이 **lemma → theorem** 패턴의 전형적 예이다:
1. 작은 사실을 `lemma`로 증명
2. `rw`로 `lemma`를 **치환**하여 `theorem` 완성

</details>

---

## 📋 9J.7 6장 전체 공식 총정리표

| 유형 | 공식 | Lean 4 표현 |
|------|------|------------|
| r-순열 (반복 불허) | n!/(n-r)! | `Nat.descFactorial n r` |
| r-조합 (반복 불허) | C(n,r) | `Nat.choose n r` |
| r-순열 (반복 허용) | nʳ | `card (Fin r → Fin n)` |
| r-조합 (반복 허용) | C(n+r-1, r) | `Nat.choose (n+r-1) r` |
| 다항 계수 | n!/(n₁!⋯nₖ!) | `Nat.multinomial` |
| 구별 객체→구별 상자 | kⁿ (다항 계수) | `card (Fin n → Fin k)` |
| 구별 불가→구별 상자 | C(n+k-1, n) | `Nat.choose (n+k-1) n` |

---

## 📋 9J.8 이 파트에서 사용한 전술 요약

| 전술 | 용도 | 이 파트에서의 사용 |
|------|------|------------------|
| `simp` | 간소화 규칙 자동 적용 | `card (Fin r → Fin n) = n^r` |
| `norm_num` | 구체적 숫자 계산 | `26^3 = 17576` |
| `native_decide` | 결정 가능 명제 자동 판정 | `Nat.choose 11 5 = 462` |
| `decide` | 결정 가능 명제 (작은 것) | 리스트 비교 |
| `rw [h]` | 등식으로 치환 | `rw [choose_zero]` |
| `omega` | 자연수/정수 선형 산술 | 방정식 풀이 |

---

## 🔗 시리즈 전체 지도

| 파트 | 내용 | Rosen 절 |
|------|------|---------|
| 9-A | 계수 기본 원리 (곱셈/덧셈 법칙) | §6.1 |
| 9-B | 비둘기집 원리 | §6.2 |
| 9-C | 비둘기집 원리 심화 | §6.2 |
| 9-D | 순열과 조합 | §6.3 |
| 9-E | 이항 정리와 파스칼 삼각형 | §6.4 |
| 9-F | 일반화된 순열과 조합 기초 | §6.5.1~6.5.3 |
| 9-G | 객체를 상자에 분배하기, 분할 | §6.5.4~6.5.5 |
| 9-H | 순열과 조합의 생성 | §6.6 |
| **9-I** | **Lean 4 기초: lemma, theorem, rw, →, ↔** | **MIL Ch.2~3** |
| **9-J** | **일반화된 순열/조합 Lean 4 형식화** | **§6.5~6.6** |
