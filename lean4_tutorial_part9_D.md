# Lean4 완전 정복 가이드 —  — Part 9-D: 순열과 조합 (Permutations and Combinations)

> **시리즈 위치**: Rosen 이산수학 8판 §6.3  
> **선수 지식**: Part 9-A (곱셈·덧셈 법칙), Part 9-B (뺄셈·나눗셈 법칙), Part 9-C (비둘기집 원리)  
> **목표**: **순열**(permutation)과 **조합**(combination)의 개념을 이해하고, Lean 4로 관련 정리들을 증명한다.

---

## 9D.0 이 장에서 배울 것

이 장은 **계수**(counting)의 핵심 도구인 **순열**(permutation)과 **조합**(combination)을 다룬다. 간단히 말하면:

- **순열**: 원소들을 **순서를 고려하여** 나열하는 방법의 수
- **조합**: 원소들을 **순서 없이** 선택하는 방법의 수

일상적인 예를 들어보자. 5명의 학생 중에서 3명을 뽑아 줄을 세우는 것은 **순열**이다 (누가 1번째, 2번째, 3번째인지가 중요하다). 반면 5명 중에서 3명을 뽑아 팀을 구성하는 것은 **조합**이다 (누가 먼저 뽑혔는지는 상관없다).

이 차이를 수학적으로 정확하게 이해하고, Lean 4에서 `Nat.factorial`, `Nat.choose`, `Fintype.card`, `Fin` 등을 활용하여 형식적으로 증명하는 방법을 배운다.

---

## 9D.1 사전 준비: Lean 4에서 팩토리얼과 기본 도구

### 9D.1.1 **팩토리얼**(Factorial)이란?

**팩토리얼**(factorial)은 1부터 n까지의 모든 자연수를 곱한 값이다. 기호로 `n!`이라 쓴다.

$$
n! = n \times (n-1) \times (n-2) \times \cdots \times 2 \times 1
$$

특별히 `0! = 1`로 정의한다. 이것은 "아무것도 선택하지 않는 방법은 딱 1가지"라는 뜻이다.

| n | n! |
|---|-----|
| 0 | 1 |
| 1 | 1 |
| 2 | 2 |
| 3 | 6 |
| 4 | 24 |
| 5 | 120 |

### 9D.1.2 Lean 4에서의 팩토리얼

Lean 4의 Mathlib에서 팩토리얼은 `Nat.factorial`로 정의되어 있다. `n!`이라는 표기법도 사용할 수 있다.

```lean
import Mathlib

-- 기본 계산
#eval Nat.factorial 0   -- 1
#eval Nat.factorial 1   -- 1
#eval Nat.factorial 5   -- 120
#eval Nat.factorial 10  -- 3628800

-- n!은 Nat.factorial n의 표기법이다
#eval (5 : ℕ).factorial  -- 120
```

### 9D.1.3 팩토리얼의 **재귀적 정의**(Recursive Definition)

팩토리얼은 다음과 같이 **재귀적**(recursive)으로 정의된다:

- `0! = 1` (기저 조건)
- `(n+1)! = (n+1) × n!` (재귀 단계)

이것을 Lean 4에서 직접 정의하면 다음과 같다:

```lean
-- Lean의 Mathlib 정의를 따라한 것 (실제로는 Nat.factorial 사용)
def myFactorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * myFactorial n
```

### 9D.1.4 팩토리얼의 기본 성질

```lean
import Mathlib

-- (1) 0! = 1
example : Nat.factorial 0 = 1 := by simp [Nat.factorial]

-- (2) (n+1)! = (n+1) * n!
example (n : ℕ) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  simp [Nat.factorial]

-- (3) n! > 0 (팩토리얼은 항상 양수)
example (n : ℕ) : 0 < Nat.factorial n := Nat.factorial_pos n

-- (4) 구체적인 계산
example : Nat.factorial 5 = 120 := by native_decide
example : Nat.factorial 3 = 6 := by native_decide
```

---

## 9D.2 **순열**(Permutation): 순서가 있는 배열

### 9D.2.1 순열이란 무엇인가?

서로 다른 원소들의 집합에서, 원소들의 **순서적인 배열**(ordered arrangement)을 **순열**(permutation)이라 한다.

> **정의**: 집합 S의 원소들을 일렬로 나열하는 방법을 S의 **순열**이라 한다. 특히, n개의 원소 중에서 r개를 뽑아 순서대로 나열하는 것을 **r-순열**(r-permutation)이라 한다.

### 9D.2.2 교재 예제 1: 사진 찍기

> **문제**: 다섯 명의 학생들 중에서 사진을 찍기 위해 세 명을 골라내 줄 세우는 방법의 수는 얼마인가? 또한, 다섯 명을 모두 줄 세우는 방법의 수는?

**풀이**:

세 명을 뽑아 줄 세우는 경우: 학생을 선택하는 **순서가 의미 있다**. 

- 첫 번째 학생: 5가지 선택
- 두 번째 학생: 4가지 선택 (첫 번째와 다른 사람)
- 세 번째 학생: 3가지 선택

**곱셈 법칙**(product rule)에 의해: `5 × 4 × 3 = 60`가지

다섯 명을 모두 줄 세우는 경우: `5 × 4 × 3 × 2 × 1 = 5! = 120`가지

```lean
-- 5명에서 3명을 뽑아 줄 세우기: P(5,3) = 60
example : 5 * 4 * 3 = 60 := by norm_num

-- 5명 전부 줄 세우기: 5! = 120
example : Nat.factorial 5 = 120 := by native_decide
```

### 9D.2.3 **r-순열의 수**: P(n, r)

n개의 서로 다른 원소로 이루어진 집합에서 r개를 선택하여 순서대로 나열하는 방법의 수를 `P(n, r)`로 표기한다.

> **정리 1** (Rosen 정리 1): n개의 서로 다른 원소로 이루어진 집합에서의 r-순열의 개수 P(n, r)은  
> $$P(n, r) = n(n-1)(n-2)\cdots(n-r+1)$$  
> 이다.

이 공식의 의미를 하나하나 따져보자:

- 첫 번째 위치: n가지 선택
- 두 번째 위치: n-1가지 선택 (하나가 이미 사용됨)
- 세 번째 위치: n-2가지 선택
- ...
- r번째 위치: n-r+1가지 선택

**곱셈 법칙**을 적용하면 위의 공식이 나온다.

### 9D.2.4 **따름정리**(Corollary) 1: 팩토리얼 표현

> **따름정리 1**: n과 r이 0 ≤ r ≤ n인 정수이면  
> $$P(n, r) = \frac{n!}{(n-r)!}$$  
> 이다.

**왜 이렇게 되는가?** 직접 확인해보자:

$$P(n, r) = n(n-1)\cdots(n-r+1) = \frac{n!}{(n-r)!}$$

예를 들어, P(5, 3)을 계산하면:

$$P(5, 3) = \frac{5!}{(5-3)!} = \frac{5!}{2!} = \frac{120}{2} = 60$$

```lean
-- P(n, r) = n! / (n-r)! 를 Lean에서 확인
-- Lean에서는 Nat.descFactorial을 사용한다
-- n.descFactorial r = n * (n-1) * ... * (n-r+1)

#eval Nat.descFactorial 5 3  -- 60  (= 5 * 4 * 3)
#eval Nat.descFactorial 8 3  -- 336 (= 8 * 7 * 6)

-- 팩토리얼과의 관계
example : Nat.descFactorial 5 3 = Nat.factorial 5 / Nat.factorial 2 := by native_decide
```

### 9D.2.5 Lean 4에서 순열의 수를 다루는 방법

Lean 4의 Mathlib에는 `Nat.descFactorial`이라는 함수가 있다. 이것은 **하강 팩토리얼**(descending factorial)로, 정확히 P(n, r)에 해당한다.

```lean
-- Nat.descFactorial n r = n * (n-1) * ... * (n-r+1)
-- 이것이 바로 P(n, r)이다!

-- 기본 계산
#eval Nat.descFactorial 5 0  -- 1  (아무것도 안 뽑음)
#eval Nat.descFactorial 5 1  -- 5  (하나만 뽑음)
#eval Nat.descFactorial 5 5  -- 120 (= 5!)

-- 재귀적 성질
-- descFactorial 0 0 = 1
-- descFactorial (n+1) (r+1) = (n+1) * descFactorial n r
```

### 9D.2.6 교재 예제 4: 경품 추첨

> **문제**: 100명의 사람이 참가한 경품에서 1등, 2등, 3등을 선발하는 방법은 모두 몇 가지인가?

**풀이**: 어떤 사람이 어떤 상을 받느냐가 중요하므로, 이것은 100개의 원소에서 3개를 뽑는 3-순열이다.

$$P(100, 3) = 100 \times 99 \times 98 = 970{,}200$$

```lean
-- P(100, 3) = 100 * 99 * 98 = 970200
example : Nat.descFactorial 100 3 = 970200 := by native_decide

-- 또는 직접 계산
example : 100 * 99 * 98 = 970200 := by norm_num
```

### 9D.2.7 교재 예제 5: 메달 수여

> **문제**: 경주에 참가하는 8명의 선수가 있다. 우승자는 금메달, 2등은 은메달, 3등은 동메달을 받는다. 동률은 없다고 할 때, 메달이 수여될 수 있는 서로 다른 모든 가능한 방법의 수는 얼마인가?

**풀이**: P(8, 3) = 8 × 7 × 6 = 336

```lean
example : Nat.descFactorial 8 3 = 336 := by native_decide
```

### 9D.2.8 교재 예제 6: 외판원의 도시 방문

> **문제**: 외판원이 8개의 도시를 방문하여야 한다. 특정한 도시에서 출발하되 나머지 7개의 도시는 원하는 순서대로 방문할 수 있다. 이 외판원이 8도시를 방문하는 경우의 수는 모두 몇 가지인가?

**풀이**: 첫 번째 도시는 고정이므로, 나머지 7개 도시의 순열을 구하면 된다.

$$7! = 5040$$

```lean
example : Nat.factorial 7 = 5040 := by native_decide
```

### 9D.2.9 교재 예제 7: 문자열 ABC 포함

> **문제**: ABCDEFGH의 순열 중에서 ABC 문자열을 포함하는 것은 모두 몇 개인가?

**풀이**: ABC 문자열을 하나의 블록으로 나타내야 하므로, {ABC}, D, E, F, G, H의 6개 객체의 순열을 구하면 된다. 6개 원소의 순열은 6! = 720가지이다.

```lean
example : Nat.factorial 6 = 720 := by native_decide
```

---

## 9D.3 Lean 4에서 순열을 형식화하기

### 9D.3.1 `Fin n`과 함수로 표현하는 순열

Lean 4에서 순열을 가장 자연스럽게 표현하는 방법은 `Equiv.Perm (Fin n)` 타입을 사용하는 것이다. 이것은 `Fin n` 위의 **전단사 함수**(bijection), 즉 `{0, 1, ..., n-1}`을 자기 자신으로 보내는 일대일 대응이다.

```lean
import Mathlib

-- Fin 3 = {0, 1, 2}
-- Equiv.Perm (Fin 3)은 {0,1,2}의 모든 순열을 나타내는 타입이다

-- 순열의 개수는 n!
example : Fintype.card (Equiv.Perm (Fin 3)) = Nat.factorial 3 := by
  simp [Fintype.card_perm]

-- 즉, 3개 원소의 순열은 6가지
example : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  simp [Fintype.card_perm]
  native_decide
```

### 9D.3.2 **핵심 정리**: n개 원소의 전체 순열의 수는 n!

이것은 Lean 4에서 `Fintype.card_perm`이라는 이름으로 증명되어 있다:

```lean
-- Fintype.card_perm : Fintype.card (Equiv.Perm α) = Nat.factorial (Fintype.card α)

-- 예시: 5개 원소의 전체 순열의 수
example : Fintype.card (Equiv.Perm (Fin 5)) = 120 := by
  simp [Fintype.card_perm]
  native_decide
```

### 9D.3.3 r-순열을 Lean 4에서 표현하기

r-순열은 "n개에서 r개를 뽑아 순서대로 나열"하는 것이다. 이것을 Lean 4에서는 **단사 함수**(injective function) `Fin r → Fin n`으로 표현할 수 있다. 즉, r개의 위치 각각에 n개의 원소 중 하나를 배정하되 중복 없이 배정하는 것이다.

```lean
-- Fin r에서 Fin n으로의 단사 함수의 수 = P(n, r)

-- 구체적인 확인: P(5,3) = 60
-- Fin 3 → Fin 5 인 단사 함수의 개수
-- (이것은 직접 세기는 복잡하므로, 공식을 확인한다)
example : Nat.descFactorial 5 3 = 60 := by native_decide
```

---

## 9D.4 **조합**(Combination): 순서 없는 선택

### 9D.4.1 조합이란 무엇인가?

**순열**이 순서를 고려한 배열이라면, **조합**은 순서를 무시한 **선택**이다.

> **정의**: 어떤 집합에서 r개의 원소를 **순서 없이** 선택하는 것을 그 집합의 원소들의 **r-조합**(r-combination)이라 부른다. 결국 r-조합은 r개 원소를 가진 집합의 한 **부분집합**(subset)에 해당된다.

핵심적인 차이를 예로 들어보자:

| 상황 | 순열인가 조합인가? | 이유 |
|------|------------|------|
| 5명 중 3명을 뽑아 **줄 세우기** | 순열 | 순서가 중요 |
| 5명 중 3명으로 **팀 구성** | 조합 | 순서가 무관 |
| 비밀번호 4자리 설정 | 순열 | 순서가 중요 (1234 ≠ 4321) |
| 카드 5장 뽑기 | 조합 | 순서가 무관 |

### 9D.4.2 교재 예제 8: 학생 선택

> **문제**: 네 명의 학생들로부터 세 명의 학생들을 선택해내는 방법의 수는 몇 가지인가?

**풀이**: 이 문제는 네 명의 학생들의 집합에서부터 세 명의 학생들을 포함시키는 부분집합의 개수를 구하는 문제와 동일하다. 모두 4개의 부분집합이 가능하다 (전체에서 한 명의 학생을 제외시키는 방법과 동일).

### 9D.4.3 교재 예제 9

> S = {1, 2, 3, 4}라 하면, {1, 3, 4}는 S의 3-조합이다. (집합 내에서 원소들 간의 순서는 의미가 없으므로 {4, 1, 3}은 {1, 3, 4}와 완전히 동일한 3-조합임을 기억하자.)

### 9D.4.4 조합의 수: C(n, r)

n개의 서로 다른 원소로 이루어진 집합에서의 r-조합의 개수는 `C(n, r)`로 표기한다. 또한 $\binom{n}{r}$로 표기하여 **이항 계수**(binomial coefficient)라고도 부른다.

> **정리 2** (Rosen 정리 2): 0 ≤ r ≤ n일 때, n개의 서로 다른 원소로 이루어진 집합에서 r-조합의 개수 C(n, r)은  
> $$C(n, r) = \frac{n!}{r!(n-r)!}$$  
> 이다.

### 9D.4.5 왜 이 공식이 성립하는가?

이 공식을 이해하는 가장 좋은 방법은 **순열과 조합의 관계**를 생각하는 것이다.

r-순열 P(n, r)은 **두 단계**로 이루어진다:
1. 먼저 n개에서 r개를 **선택**한다 → C(n, r)가지
2. 선택한 r개를 **순서대로 배열**한다 → r!가지

따라서 **곱셈 법칙**에 의해:

$$P(n, r) = C(n, r) \times r!$$

이것을 C(n, r)에 대해 풀면:

$$C(n, r) = \frac{P(n, r)}{r!} = \frac{n!/(n-r)!}{r!} = \frac{n!}{r!(n-r)!}$$

이것이 바로 정리 2의 공식이다! 매우 아름다운 관계이다.

```
순열 = 조합 × 배열
P(n,r) = C(n,r) × P(r,r)
P(n,r) = C(n,r) × r!
```

### 9D.4.6 Lean 4에서의 조합: `Nat.choose`

Lean 4에서 C(n, r)은 `Nat.choose n r`로 표현한다. 이것은 $\binom{n}{r}$에 해당한다.

```lean
import Mathlib

-- 기본 계산
#eval Nat.choose 4 2   -- 6
#eval Nat.choose 5 3   -- 10
#eval Nat.choose 10 5  -- 252
#eval Nat.choose 52 5  -- 2598960

-- 경계 사례
#eval Nat.choose 5 0   -- 1  (아무것도 안 뽑음)
#eval Nat.choose 5 5   -- 1  (전부 뽑음)
#eval Nat.choose 3 5   -- 0  (뽑을 수 있는 것보다 많이 뽑으려 함)
```

---

## 9D.5 조합의 핵심 성질과 Lean 4 증명

### 9D.5.1 C(n, 0) = 1 과 C(n, n) = 1

아무것도 선택하지 않는 방법은 딱 1가지 (공집합), 전부 선택하는 방법도 딱 1가지이다.

```lean
-- C(n, 0) = 1
example (n : ℕ) : Nat.choose n 0 = 1 := Nat.choose_zero_right n

-- C(n, n) = 1
example (n : ℕ) : Nat.choose n n = 1 := Nat.choose_self n
```

#### 🏋️ 연습 9D-1: 경계값 확인 (괄호 채우기)

```lean
-- Nat.choose의 경계값을 확인해보자
example : Nat.choose 7 0 = ⟨___⟩ := by native_decide
example : Nat.choose 7 7 = ⟨___⟩ := by native_decide
example : Nat.choose 7 1 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 7 0 = 1 := by native_decide
example : Nat.choose 7 7 = 1 := by native_decide
example : Nat.choose 7 1 = 7 := by native_decide
```

**해설**: C(7,0) = 1 (공집합), C(7,7) = 1 (전체집합), C(7,1) = 7 (원소 하나씩 선택)이다.

</details>

### 9D.5.2 **따름정리 2**: C(n, r) = C(n, n-r)

> **따름정리 2**: n과 r이 양의 정수이고 r ≤ n이면, C(n, r) = C(n, n-r)이다.

이것의 직관적 의미: n개에서 r개를 **선택하는** 것은 n개에서 n-r개를 **제외하는** 것과 같다!

예를 들어, 52장의 카드에서 5장을 뽑는 방법의 수 C(52, 5)는 52장에서 47장을 뽑는 방법의 수 C(52, 47)과 같다. 5장을 뽑는 것 = 47장을 남기는 것이기 때문이다.

**증명** (대수적):

$$C(n, r) = \frac{n!}{r!(n-r)!}$$

$$C(n, n-r) = \frac{n!}{(n-r)!(n-(n-r))!} = \frac{n!}{(n-r)!r!}$$

따라서 C(n, r) = C(n, n-r)이다.

```lean
-- 따름정리 2: C(n, r) = C(n, n-r)
-- Lean에서는 Nat.choose_symm_diff라는 이름이다
example (n : ℕ) (h : 5 ≤ n) : Nat.choose n 5 = Nat.choose n (n - 5) := by
  exact Nat.choose_symm h

-- 구체적인 예
example : Nat.choose 52 5 = Nat.choose 52 47 := by native_decide
example : Nat.choose 10 3 = Nat.choose 10 7 := by native_decide
```

#### 🏋️ 연습 9D-2: 대칭성 확인 (괄호 채우기)

```lean
-- C(n, r) = C(n, n-r)를 구체적인 값으로 확인해보자
example : Nat.choose 8 3 = Nat.choose 8 ⟨___⟩ := by native_decide
example : Nat.choose 12 4 = Nat.choose 12 ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 8 3 = Nat.choose 8 5 := by native_decide
example : Nat.choose 12 4 = Nat.choose 12 8 := by native_decide
```

**해설**: C(8, 3) = C(8, 8-3) = C(8, 5)이고, C(12, 4) = C(12, 12-4) = C(12, 8)이다.

</details>

### 9D.5.3 교재 예제 10: 부분집합의 수

> **문제**: 집합 {a, b, c, d}의 2-조합은 6개의 부분집합 {a, b}, {a, c}, {a, d}, {b, c}, {b, d}, {c, d}이므로 C(4, 2) = 6이다.

```lean
example : Nat.choose 4 2 = 6 := by native_decide
```

### 9D.5.4 교재 예제 11: 포커 카드

> **문제**: 52장의 포커 카드로부터 5장의 카드를 갖는 방법의 수는 몇 가지인가? 또한, 52장으로부터 47장의 카드를 선택하는 방법의 수는 몇 가지인가?

**풀이**: 카드가 주어지는 순서는 문제가 되지 않으므로 조합 정리에 의해:

$$C(52, 5) = \frac{52!}{5! \cdot 47!} = \frac{52 \cdot 51 \cdot 50 \cdot 49 \cdot 48}{5 \cdot 4 \cdot 3 \cdot 2 \cdot 1} = 2{,}598{,}960$$

그리고 C(52, 47) = C(52, 5) = 2,598,960이다.

```lean
example : Nat.choose 52 5 = 2598960 := by native_decide
example : Nat.choose 52 47 = 2598960 := by native_decide

-- 이 둘이 같다는 것은 따름정리 2에 의한다
example : Nat.choose 52 5 = Nat.choose 52 47 := by native_decide
```

### 9D.5.5 교재 예제 12: 테니스 팀 선발

> **문제**: 10명의 선수로 된 테니스 팀에서 시합에 출전할 5명의 선수를 선발하는 방법의 수는 모두 몇 가지인가?

**풀이**: C(10, 5) = 252

```lean
example : Nat.choose 10 5 = 252 := by native_decide
```

### 9D.5.6 교재 예제 13: 우주비행사 선발

> **문제**: 화성으로 항해할 임무를 띤 우주비행사로서 30명이 훈련을 받아 왔다. 모든 승무원들이 같은 임무를 띠고 있다고 가정할 때 6명의 승무원을 선발하는 방법은 모두 몇 가지인가?

**풀이**: C(30, 6) = 593,775

```lean
example : Nat.choose 30 6 = 593775 := by native_decide
```

### 9D.5.7 교재 예제 14: 비트 문자열

> **문제**: 길이 n인 비트 문자열 중에서 1을 정확히 r개 포함하고 있는 것은 모두 몇 개인가?

**풀이**: 길이 n인 비트 문자열에서 r개의 위치를 선택하는 것은 집합 {1, 2, 3, ..., n}의 r-조합을 만든다. 따라서 답은 C(n, r)개이다.

```lean
-- 길이 10인 비트 문자열에서 1이 정확히 3개인 것의 수
example : Nat.choose 10 3 = 120 := by native_decide

-- 길이 8인 비트 문자열에서 1이 정확히 4개인 것의 수
example : Nat.choose 8 4 = 70 := by native_decide
```

### 9D.5.8 교재 예제 15: 위원회 구성 (곱셈 법칙 + 조합)

> **문제**: 이산수학 과목을 개발하기 위한 위원회를 구성하려고 한다. 수학과 교수가 9명, 전산과 교수가 11명일 때, 수학과 교수 3명, 전산과 교수 4명으로 위원회를 구성하는 방법은 모두 몇 가지인가?

**풀이**: **곱셈 법칙**에 의해서, 원소 9개의 집합에 대한 3-조합과 원소 11개의 집합에 대한 4-조합의 수를 곱하면 된다.

$$C(9, 3) \cdot C(11, 4) = 84 \cdot 330 = 27{,}720$$

```lean
example : Nat.choose 9 3 * Nat.choose 11 4 = 27720 := by native_decide
```

---

## 9D.6 조합 증명의 핵심: 조합적 증명

### 9D.6.1 **조합 증명**(Combinatorial Proof)이란?

**정의 1** (Rosen 정의 1): 항등식에 대한 **조합 증명**(combinatorial proof)이란 항등식에서의 양변 각각이 비록 서로 다른 방식으로 셈하고는 있지만 그 결과가 같음을 증명하기 위해 계수적 방법들을 사용하는 증명법이다.

쉽게 말하면, **같은 것을 두 가지 다른 방법으로 세어서 두 식이 같음을 보이는** 증명 방법이다!

예를 들어, 따름정리 2 `C(n, r) = C(n, n-r)`의 조합 증명:

- **왼쪽** C(n, r): n개에서 r개를 **선택하는** 방법의 수
- **오른쪽** C(n, n-r): n개에서 n-r개를 **선택하는** 방법의 수

그런데 "r개를 선택하는 것"과 "나머지 n-r개를 선택하는 것"은 **정확히 같은 것**이다! (r개를 선택하면 자동으로 n-r개가 선택되지 않은 것으로 결정되기 때문.) 따라서 C(n, r) = C(n, n-r)이다.

### 9D.6.2 Lean 4에서 조합 증명 맛보기

```lean
import Mathlib

-- C(n, r) = C(n, n-r)의 Lean 증명
-- Mathlib에서는 Nat.choose_symm로 제공된다
example (n r : ℕ) (h : r ≤ n) : Nat.choose n r = Nat.choose n (n - r) := by
  exact Nat.choose_symm h
```

---

## 9D.7 Lean 4에서 Finset.card와 choose의 관계

### 9D.7.1 부분집합의 수와 choose

Lean 4에서 유한 집합의 크기가 k인 부분집합의 수를 세는 것은 `Nat.choose`와 직접적으로 연결된다.

```lean
import Mathlib

-- Finset.card (Finset.powersetCard k s) = Nat.choose (Finset.card s) k
-- 즉, 크기 k인 부분집합의 수 = C(|s|, k)

-- 구체적인 예: {0,1,2,3}의 크기 2인 부분집합의 수
example : (Finset.range 4).powersetCard 2 |>.card = 6 := by native_decide

-- 이것은 C(4, 2) = 6과 같다
example : Nat.choose 4 2 = 6 := by native_decide
```

### 9D.7.2 `Finset.powersetCard`의 의미

`Finset.powersetCard k s`는 유한 집합 `s`의 모든 **크기 k인 부분집합**들의 집합이다.

```lean
-- powersetCard k s = {t ⊆ s | #t = k}
-- 원소의 수는 choose (#s) k

open Finset in
example (n k : ℕ) : (range n).powersetCard k |>.card = Nat.choose n k := by
  simp [card_powersetCard]
```

---

## 9D.8 종합 연습문제

### 🏋️ 연습 9D-3: 기본 계산 (괄호 채우기)

```lean
-- 다음 값을 계산하여 빈칸을 채워라
-- (교재 연습문제 5, 6 기반)

-- P(6, 3) = ?
example : Nat.descFactorial 6 3 = ⟨___⟩ := by native_decide

-- P(6, 5) = ?
example : Nat.descFactorial 6 5 = ⟨___⟩ := by native_decide

-- P(8, 1) = ?
example : Nat.descFactorial 8 1 = ⟨___⟩ := by native_decide

-- C(5, 1) = ?
example : Nat.choose 5 1 = ⟨___⟩ := by native_decide

-- C(5, 3) = ?
example : Nat.choose 5 3 = ⟨___⟩ := by native_decide

-- C(8, 4) = ?
example : Nat.choose 8 4 = ⟨___⟩ := by native_decide

-- C(8, 0) = ?
example : Nat.choose 8 0 = ⟨___⟩ := by native_decide

-- C(12, 6) = ?
example : Nat.choose 12 6 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- P(6, 3) = 6 × 5 × 4 = 120
example : Nat.descFactorial 6 3 = 120 := by native_decide

-- P(6, 5) = 6 × 5 × 4 × 3 × 2 = 720
example : Nat.descFactorial 6 5 = 720 := by native_decide

-- P(8, 1) = 8
example : Nat.descFactorial 8 1 = 8 := by native_decide

-- C(5, 1) = 5
example : Nat.choose 5 1 = 5 := by native_decide

-- C(5, 3) = 10
example : Nat.choose 5 3 = 10 := by native_decide

-- C(8, 4) = 70
example : Nat.choose 8 4 = 70 := by native_decide

-- C(8, 0) = 1
example : Nat.choose 8 0 = 1 := by native_decide

-- C(12, 6) = 924
example : Nat.choose 12 6 = 924 := by native_decide
```

</details>

### 🏋️ 연습 9D-4: 순열의 수 (교재 연습문제 2, 3 기반)

```lean
-- 집합 {a, b, c, d, e, f, g}의 순열은 모두 몇 개인가?
example : Nat.factorial 7 = ⟨___⟩ := by native_decide

-- 집합 {a, b, c, d, e, f, g}의 순열 중에서 a로 끝나는 것은 모두 몇 개인가?
-- (a를 마지막에 고정하면, 나머지 6개의 순열이다)
example : Nat.factorial 6 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- 7개 원소의 전체 순열: 7! = 5040
example : Nat.factorial 7 = 5040 := by native_decide

-- a로 끝나는 순열: 나머지 6개의 순열 = 6! = 720
example : Nat.factorial 6 = 720 := by native_decide
```

**해설**: 마지막 자리가 a로 고정되면, 나머지 6개의 원소를 앞의 6자리에 배열하는 것이므로 6! = 720이다.

</details>

### 🏋️ 연습 9D-5: 3-순열과 3-조합 나열 (교재 연습문제 4 기반)

```lean
-- S = {1, 2, 3, 4, 5}라 하자.
-- S의 3-순열의 수 P(5, 3) = ?
example : Nat.descFactorial 5 3 = ⟨___⟩ := by native_decide

-- S의 3-조합의 수 C(5, 3) = ?
example : Nat.choose 5 3 = ⟨___⟩ := by native_decide

-- P(5,3) = C(5,3) × 3! 인지 확인하라
example : Nat.descFactorial 5 3 = Nat.choose 5 3 * Nat.factorial 3 := by ⟨___⟩
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- P(5, 3) = 60
example : Nat.descFactorial 5 3 = 60 := by native_decide

-- C(5, 3) = 10
example : Nat.choose 5 3 = 10 := by native_decide

-- P(5,3) = C(5,3) × 3!
-- 60 = 10 × 6 ✓
example : Nat.descFactorial 5 3 = Nat.choose 5 3 * Nat.factorial 3 := by native_decide
```

**해설**: 순열 = 조합 × 배열이라는 핵심 관계 P(n,r) = C(n,r) × r!을 확인할 수 있다.

</details>

### 🏋️ 연습 9D-6: 5-조합의 수 (교재 연습문제 7 기반)

```lean
-- 원소 9개의 집합에 대한 5-조합의 수를 계산하라
example : Nat.choose 9 5 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.choose 9 5 = 126 := by native_decide
```

**해설**: C(9, 5) = 9! / (5! × 4!) = 126이다. 참고로 C(9, 5) = C(9, 4) = 126이기도 하다 (대칭성).

</details>

### 🏋️ 연습 9D-7: 경마 순위 (교재 연습문제 8 기반)

```lean
-- 같은 등수가 없을 경우, 5명의 주자가 경주를 마치는 서로 다른 순서의 경우의 수는?
-- (5명 전체의 순열)
example : Nat.factorial 5 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.factorial 5 = 120 := by native_decide
```

</details>

### 🏋️ 연습 9D-8: 경마 메달 (교재 연습문제 9 기반)

```lean
-- 12마리의 말이 참가하는 경마에서 1, 2, 3등이 결정되는 가능성은 모두 몇 가지인가?
-- P(12, 3) = ?
example : Nat.descFactorial 12 3 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.descFactorial 12 3 = 1320 := by native_decide
```

**해설**: P(12, 3) = 12 × 11 × 10 = 1320이다.

</details>

### 🏋️ 연습 9D-9: 투표 용지 (교재 연습문제 10 기반)

```lean
-- 어떤 주의 상원 의원 후보가 6명 있다.
-- 투표 용지에 후보자의 이름을 서로 다른 순서로 인쇄하는 경우의 수는?
example : Nat.factorial 6 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Nat.factorial 6 = 720 := by native_decide
```

</details>

### 🏋️ 연습 9D-10: 비트 문자열 (교재 연습문제 11 기반)

```lean
-- 길이 10인 비트 문자열 중 다음을 포함하고 있는 것은 모두 몇 개인가?

-- a) 4개의 1: C(10, 4) = ?
example : Nat.choose 10 4 = ⟨___⟩ := by native_decide

-- b) 4개 이하의 1: C(10,0) + C(10,1) + C(10,2) + C(10,3) + C(10,4) = ?
example : Nat.choose 10 0 + Nat.choose 10 1 + Nat.choose 10 2 +
          Nat.choose 10 3 + Nat.choose 10 4 = ⟨___⟩ := by native_decide

-- c) 4개 이상의 1: 전체 - (3개 이하의 1) = 2^10 - (C(10,0)+C(10,1)+C(10,2)+C(10,3))
example : 2^10 - (Nat.choose 10 0 + Nat.choose 10 1 +
          Nat.choose 10 2 + Nat.choose 10 3) = ⟨___⟩ := by native_decide

-- d) 동일한 수의 0과 1: C(10, 5) = ?
example : Nat.choose 10 5 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- a) C(10, 4) = 210
example : Nat.choose 10 4 = 210 := by native_decide

-- b) 386
example : Nat.choose 10 0 + Nat.choose 10 1 + Nat.choose 10 2 +
          Nat.choose 10 3 + Nat.choose 10 4 = 386 := by native_decide

-- c) 2^10 - 176 = 1024 - 176 = 848
example : 2^10 - (Nat.choose 10 0 + Nat.choose 10 1 +
          Nat.choose 10 2 + Nat.choose 10 3) = 848 := by native_decide

-- d) C(10, 5) = 252
example : Nat.choose 10 5 = 252 := by native_decide
```

**해설**:
- a) 10자리 중 1이 들어갈 4자리를 고른다: C(10, 4) = 210
- b) 1이 0개~4개인 경우를 모두 합한다: 1 + 10 + 45 + 120 + 210 = 386
- c) 전체(2^10=1024)에서 1이 0~3개인 경우(176)를 빼면: 1024 - 176 = 848
- d) 0과 1이 5개씩이므로 C(10, 5) = 252

</details>

### 🏋️ 연습 9D-11: 소프트볼 팀 (교재 연습문제 28 기반)

```lean
-- 소프트볼 경기에 출전하기 위해서 13명이 모였다.

-- a) 시합에 나갈 10명의 선수를 고르는 방법의 수: C(13, 10) = ?
example : Nat.choose 13 10 = ⟨___⟩ := by native_decide

-- b) 13명 중에서 10명을 뽑아 각 포지션별로 할당하는 방법: P(13, 10) = ?
example : Nat.descFactorial 13 10 = ⟨___⟩ := by native_decide
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- a) C(13, 10) = C(13, 3) = 286
example : Nat.choose 13 10 = 286 := by native_decide

-- b) P(13, 10) = 13! / 3! = 1037836800
example : Nat.descFactorial 13 10 = 1037836800 := by native_decide
```

**해설**:
- a) 팀 선발은 **조합** (순서 무관): C(13, 10) = 286
- b) 포지션 배정은 **순열** (순서 유관): P(13, 10) = 1,037,836,800

이것이 순열과 조합의 핵심적인 차이이다!

</details>

### 🏋️ 연습 9D-12: 위원회 구성 (sorry 방식) (교재 연습문제 29 기반)

```lean
-- 회원이 25명인 동아리가 있다.
-- a) 집행부 위원으로 4명을 선출하는 방법의 수
-- (순서 무관 → 조합)
example : Nat.choose 25 4 = 12650 := by sorry

-- b) 회장, 부회장, 총무, 재무를 선출하는 방법의 수
-- (순서 유관 → 순열)
example : Nat.descFactorial 25 4 = 303600 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- a) C(25, 4) = 12650
example : Nat.choose 25 4 = 12650 := by native_decide

-- b) P(25, 4) = 25 × 24 × 23 × 22 = 303600
example : Nat.descFactorial 25 4 = 303600 := by native_decide
```

**해설**: a)에서는 4명을 뽑기만 하면 되므로 조합, b)에서는 누가 회장, 부회장인지가 중요하므로 순열이다.

</details>

### 🏋️ 연습 9D-13: 순열 vs 조합 관계 증명 (sorry 방식)

```lean
-- P(n, r) = C(n, r) × r! 을 구체적인 값으로 확인하라

-- P(10, 3) = C(10, 3) × 3!
example : Nat.descFactorial 10 3 = Nat.choose 10 3 * Nat.factorial 3 := by sorry

-- P(8, 5) = C(8, 5) × 5!
example : Nat.descFactorial 8 5 = Nat.choose 8 5 * Nat.factorial 5 := by sorry

-- P(20, 4) = C(20, 4) × 4!
example : Nat.descFactorial 20 4 = Nat.choose 20 4 * Nat.factorial 4 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
-- 모두 native_decide로 증명 가능
example : Nat.descFactorial 10 3 = Nat.choose 10 3 * Nat.factorial 3 := by native_decide
example : Nat.descFactorial 8 5 = Nat.choose 8 5 * Nat.factorial 5 := by native_decide
example : Nat.descFactorial 20 4 = Nat.choose 20 4 * Nat.factorial 4 := by native_decide
```

**해설**: P(n, r) = C(n, r) × r!은 순열과 조합의 가장 근본적인 관계이다. 각각 구체적인 값을 넣으면:
- 720 = 120 × 6
- 6720 = 56 × 120
- 116280 = 4845 × 24

</details>

### 🏋️ 연습 9D-14: Perm의 카디널리티 (sorry 방식)

```lean
import Mathlib

-- n개 원소의 전체 순열의 수가 n!임을 확인하라
-- Fin n의 순열 수 = n!
example : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by sorry
example : Fintype.card (Equiv.Perm (Fin 6)) = 720 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  simp [Fintype.card_perm]
  native_decide

example : Fintype.card (Equiv.Perm (Fin 6)) = 720 := by
  simp [Fintype.card_perm]
  native_decide
```

**해설**: `Fintype.card_perm` 정리가 `Fintype.card (Equiv.Perm α) = Nat.factorial (Fintype.card α)`을 말해주므로, `simp`로 이것을 적용한 뒤 `native_decide`로 수치를 확인한다.

</details>

### 🏋️ 연습 9D-15: powersetCard 활용 (sorry 방식)

```lean
import Mathlib
open Finset

-- {0, 1, 2, 3, 4}의 크기 3인 부분집합의 수가 C(5, 3) = 10임을 증명하라
example : (range 5).powersetCard 3 |>.card = 10 := by sorry
```

<details>
<summary>🔑 답 보기</summary>

```lean
example : (range 5).powersetCard 3 |>.card = 10 := by native_decide
```

또는 `card_powersetCard`를 활용할 수도 있다:

```lean
example : (range 5).powersetCard 3 |>.card = 10 := by
  rw [card_powersetCard]
  simp [card_range]
```

</details>

---

## 9D.9 이 장의 핵심 요약

| 개념 | 공식 | Lean 4 표현 | 의미 |
|------|------|-----------|------|
| **팩토리얼**(factorial) | n! | `Nat.factorial n` | 1부터 n까지의 곱 |
| **r-순열**(r-permutation) | P(n,r) = n!/(n-r)! | `Nat.descFactorial n r` | 순서 있는 선택 |
| **r-조합**(r-combination) | C(n,r) = n!/(r!(n-r)!) | `Nat.choose n r` | 순서 없는 선택 |
| **전체 순열** | P(n,n) = n! | `Fintype.card (Equiv.Perm (Fin n))` | n개의 전체 배열 |

**핵심 관계**: `P(n, r) = C(n, r) × r!`

순열은 "**뽑아서 줄 세우는 것**", 조합은 "**그냥 뽑는 것**"이라고 기억하면 된다.

### 주요 Lean 4 전술 및 함수

| 함수/전술 | 용도 |
|---------|------|
| `Nat.factorial n` | n!을 계산 |
| `Nat.descFactorial n r` | P(n, r)을 계산 |
| `Nat.choose n r` | C(n, r)을 계산 |
| `Nat.factorial_pos` | n! > 0 증명 |
| `Nat.choose_zero_right` | C(n, 0) = 1 |
| `Nat.choose_self` | C(n, n) = 1 |
| `Nat.choose_symm` | C(n, r) = C(n, n-r) |
| `Fintype.card_perm` | 순열의 수 = n! |
| `card_powersetCard` | 크기 k인 부분집합의 수 = C(n, k) |
| `native_decide` | 구체적인 수치 계산 |
| `norm_num` | 산술 계산 |

---

> **다음 편 예고**: Part 9-E에서는 **이항 정리**(Binomial Theorem)와 **파스칼 항등식**(Pascal's Identity)을 Lean 4로 다룬다.
