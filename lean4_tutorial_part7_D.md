# Lean4 완전 정복 가이드 — 제7-D편

## **소수**(Prime Numbers)와 **소인수분해**(Prime Factorization) 완전 정복

> **교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판 4.3절  
> **참고**: 『Mathematics in Lean』 Chapter 5 Elementary Number Theory  
> **선수 학습**: 제7-A편(나눗셈과 약수), 제7-B편(합동과 나머지 산술), 제7-C편(정수 표현)

---

## 7D.0 이 장의 목표

이 장에서 다루는 핵심 내용은 다음과 같다:

1. **소수**(prime)와 **합성수**(composite)의 정의 — Lean4에서 `Nat.Prime`
2. **대수학의 기본 정리**(fundamental theorem of arithmetic) — 소인수분해의 유일성
3. **직접 나누어 보기**(trial division) — 소수 판정법
4. **에라토스테네스의 체**(sieve of Eratosthenes) — 소수를 걸러내는 방법
5. **소수의 무한함** — 소수가 무한히 많다는 증명 (Lean4로!)
6. 치환/대입 = **슈퍼포지션**(superposition), **보조정리**(lemma)와 **정리**(theorem)의 관계, **→ vs ↔** 복습

---

## 7D.1 핵심 개념 복습: **정리**(theorem), **보조정리**(lemma), **→ vs ↔**

### 7D.1.1 **정리**(theorem)와 **보조정리**(lemma)는 무엇인가?

수학에서 어떤 사실을 증명하면, 그것을 **정리**(theorem)라고 부른다. 그런데 큰 정리를 증명하려면 작은 사실들을 먼저 증명해야 할 때가 많다. 이 작은 사실들을 **보조정리**(lemma)라고 부른다.

**핵심**: Lean4에서 `theorem`과 `lemma`는 **완전히 동일한 것**이다. 문법도 같고, 기능도 같다. 차이는 오직 "의도"뿐이다:

- `theorem` — "이것이 우리가 궁극적으로 보이고 싶은 주요 결과다"라는 뜻
- `lemma` — "이것은 주요 결과를 증명하기 위한 중간 단계다"라는 뜻

```lean
-- 이 둘은 Lean4에서 완전히 동일하게 작동한다
theorem myTheorem : 2 + 3 = 5 := by norm_num
lemma myLemma : 2 + 3 = 5 := by norm_num
```

실제 사용 예를 보자. "소수가 무한히 많다"를 증명할 때, 먼저 "2 이상의 자연수는 소인수를 가진다"를 보조정리로 증명하고, 이를 이용해 주요 정리를 증명한다:

```lean
-- 보조정리: 2 이상의 수는 소인수를 가진다
lemma exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p, Nat.Prime p ∧ p ∣ n := by
  sorry  -- 나중에 증명

-- 주요 정리: 소수는 무한히 많다
theorem primes_infinite : ∀ n, ∃ p, p > n ∧ Nat.Prime p := by
  sorry  -- 보조정리를 이용하여 증명
```

### 7D.1.2 **→**(if)와 **↔**(if and only if)의 차이

**→ (한 방향 조건문, if ... then ...)**

`P → Q`는 "P이면 Q이다"를 의미한다. 한쪽 방향만 성립한다.

```lean
-- "n이 6의 배수이면 n은 2의 배수이다" (참)
example (n : Nat) (h : 6 ∣ n) : 2 ∣ n := by
  obtain ⟨k, hk⟩ := h    -- n = 6 * k
  use 3 * k               -- n = 2 * (3 * k)
  omega

-- 그러나 역은 성립하지 않는다!
-- "n이 2의 배수이면 n은 6의 배수이다" (거짓: 반례 n = 4)
```

**↔ (쌍방향 조건문, if and only if)**

`P ↔ Q`는 "P이면 Q이고, Q이면 P이다"를 의미한다. 양쪽 모두 성립한다.

```lean
-- "n이 짝수 ↔ n을 2로 나눈 나머지가 0이다"
example (n : Nat) : 2 ∣ n ↔ n % 2 = 0 := by
  constructor
  · -- 정방향 (→): 2 ∣ n이면 n % 2 = 0
    intro ⟨k, hk⟩
    omega
  · -- 역방향 (←): n % 2 = 0이면 2 ∣ n
    intro h
    exact Nat.dvd_of_mod_eq_zero h
```

**↔를 증명하는 방법**: `constructor` 전술을 사용하면 목표가 두 개로 갈라진다:
- 첫 번째 목표: 정방향 (P → Q)
- 두 번째 목표: 역방향 (Q → P)

**↔를 사용하는 방법**: 
- `h.mp` 또는 `h.1` — 정방향 추출 (P → Q 부분)
- `h.mpr` 또는 `h.2` — 역방향 추출 (Q → P 부분)
- `rw [h]` — P를 Q로 치환 (↔이면 `rw`로 양방향 치환 가능!)

### 7D.1.3 치환/대입 = **슈퍼포지션**(superposition)

Lean4에서 **`rw`**(rewrite) 전술은 등식 또는 ↔를 이용하여 목표의 한 부분을 다른 것으로 "치환"한다. 이것을 수학에서는 **대입**(substitution)이라 하고, Lean4의 내부 추론 엔진에서는 **슈퍼포지션**(superposition)이라는 기법을 사용한다.

**슈퍼포지션**이란: 이미 알려진 등식 `a = b`를 사용하여, 어떤 식에서 `a`가 나타나는 부분을 `b`로 바꾸는 것이다.

```lean
-- 예: h : a = b가 있을 때
-- 목표: a + c = b + c
-- rw [h]를 적용하면 → 목표가 b + c = b + c가 되어 rfl로 해결

example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]  -- a를 b로 치환 → 목표: b + c = b + c → 자동 해결
```

**`rw`의 방향**:
- `rw [h]` — h : a = b일 때, **a → b** 방향으로 치환
- `rw [← h]` — h : a = b일 때, **b → a** 방향으로 치환 (역방향)

```lean
example (a b c : Nat) (h : a = b) : b + c = a + c := by
  rw [← h]  -- b를 a로 치환 (역방향)
```

---

## 7D.2 **소수**(Prime Number)란 무엇인가?

### 7D.2.1 수학적 정의 (Rosen 정의 1)

> **정의 1**: 1보다 큰 정수 *p*의 양의 인수가 1과 *p*뿐일 때 **소수**(prime)라고 부른다.  
> 1보다 크면서 소수가 아닌 양의 정수는 **합성수**(composite)라고 부른다.

쉽게 말하면:
- **소수**(prime): 1과 자기 자신으로만 나누어떨어지는 수 (2, 3, 5, 7, 11, 13, ...)
- **합성수**(composite): 1과 자기 자신 이외의 약수가 있는 수 (4, 6, 8, 9, 10, ...)
- **주의**: 1은 소수도 합성수도 아니다!

### 7D.2.2 Lean4에서 소수: `Nat.Prime`

Lean4의 Mathlib에는 소수를 판정하는 타입이 이미 정의되어 있다:

```lean
-- Nat.Prime의 정의를 확인해 보자
#check Nat.Prime
-- Nat.Prime p는 "p가 소수"라는 명제(Prop)이다

-- 구체적인 수가 소수인지 확인
#check Nat.Prime 2    -- 이것은 명제(Prop)이다
#check Nat.Prime 17   -- 이것도 명제(Prop)이다
```

**`Nat.Prime`의 핵심 성질 두 가지**:

```lean
-- 성질 1: 소수의 약수는 1 또는 자기 자신뿐이다
#check Nat.Prime.eq_one_or_self_of_dvd
-- Nat.Prime.eq_one_or_self_of_dvd :
--   Nat.Prime p → ∀ m, m ∣ p → m = 1 ∨ m = p

-- 성질 2: 소수는 2 이상이다
#check Nat.Prime.two_le
-- Nat.Prime.two_le : Nat.Prime p → 2 ≤ p
```

### 7D.2.3 구체적인 소수 확인 — `norm_num`과 `decide`

Lean4에서 특정 수가 소수인지 확인하는 가장 쉬운 방법은 `norm_num`이다:

```lean
-- 소수 확인
example : Nat.Prime 2 := by norm_num
example : Nat.Prime 3 := by norm_num
example : Nat.Prime 5 := by norm_num
example : Nat.Prime 7 := by norm_num
example : Nat.Prime 11 := by norm_num
example : Nat.Prime 13 := by norm_num
example : Nat.Prime 17 := by norm_num
example : Nat.Prime 101 := by norm_num

-- 합성수는 소수가 아님을 확인
example : ¬ Nat.Prime 4 := by norm_num
example : ¬ Nat.Prime 9 := by norm_num
example : ¬ Nat.Prime 15 := by norm_num
example : ¬ Nat.Prime 100 := by norm_num
example : ¬ Nat.Prime 1 := by norm_num  -- 1은 소수가 아니다!
```

Lean4에는 미리 정의된 소수 상수도 있다:

```lean
-- 2와 3은 자주 사용되므로 별도 정리가 있다
#check Nat.prime_two   -- : Nat.Prime 2
#check Nat.prime_three -- : Nat.Prime 3
```

### 연습 7D.1: 소수 판별 (괄호 채우기)

다음 빈칸을 채워서 각 수가 소수인지 합성수인지 확인하시오.

```lean
-- 연습 1: 소수 확인
example : Nat.Prime 29 := by (______)
example : Nat.Prime 97 := by (______)

-- 연습 2: 합성수 확인
example : ¬ Nat.Prime 21 := by (______)
example : ¬ Nat.Prime 111 := by (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
example : Nat.Prime 29 := by norm_num
example : Nat.Prime 97 := by norm_num

example : ¬ Nat.Prime 21 := by norm_num  -- 21 = 3 × 7
example : ¬ Nat.Prime 111 := by norm_num  -- 111 = 3 × 37
```

`norm_num`은 구체적인 수에 대한 소수 판별을 자동으로 수행한다. 내부적으로 직접 나누어보기(trial division)를 사용한다.

</details>

---

## 7D.3 소수의 핵심 성질들

### 7D.3.1 "약수가 1 또는 자기 자신뿐" — `eq_one_or_self_of_dvd`

소수의 가장 기본적인 성질: "p가 소수이고 m이 p를 나누면, m은 1이거나 p이다."

```lean
-- 이 성질을 사용하는 예
example : ∀ m : Nat, m ∣ 7 → m = 1 ∨ m = 7 := by
  intro m hm
  have h7 : Nat.Prime 7 := by norm_num
  exact h7.eq_one_or_self_of_dvd m hm

-- 직접 해보기: 7의 약수를 하나하나 확인
example : (1 : Nat) ∣ 7 := by norm_num
example : (7 : Nat) ∣ 7 := by norm_num
example : ¬ (2 : Nat) ∣ 7 := by norm_num
example : ¬ (3 : Nat) ∣ 7 := by norm_num
```

### 7D.3.2 "소수가 곱을 나누면, 인수 중 하나를 나눈다" — `Nat.Prime.dvd_mul`

이것은 소수의 매우 중요한 성질이다:

> p가 소수이고 p | ab이면, p | a 이거나 p | b이다.

```lean
#check Nat.Prime.dvd_mul
-- Nat.Prime.dvd_mul : Nat.Prime p → (p ∣ a * b ↔ p ∣ a ∨ p ∣ b)

-- 예: 3 | 12이고 12 = 4 × 3이므로, 3 | 4이거나 3 | 3이다
example : (3 : Nat) ∣ 4 ∨ (3 : Nat) ∣ 3 := by
  right
  norm_num
```

**주의**: 이 성질은 소수에서만 성립한다! 합성수에서는 성립하지 않는다:
- 6 | 12이고 12 = 4 × 3이지만, 6 ∤ 4이고 6 ∤ 3이다.

### 7D.3.3 소수는 2 이상이다 — `Nat.Prime.two_le`

```lean
-- 모든 소수는 2 이상
example (p : Nat) (hp : Nat.Prime p) : 2 ≤ p := hp.two_le

-- 이것은 1이 소수가 아니라는 것과 동치
example : ¬ Nat.Prime 0 := by norm_num
example : ¬ Nat.Prime 1 := by norm_num
```

### 연습 7D.2: 소수 성질 활용 (괄호 채우기)

```lean
-- 연습 1: 소수의 약수 성질 사용
example (m : Nat) (h : m ∣ 13) : m = 1 ∨ m = 13 := by
  have hp : Nat.Prime 13 := by (______)
  exact hp.eq_one_or_self_of_dvd m h

-- 연습 2: 소수는 2 이상
example : 2 ≤ 41 := by
  have hp : Nat.Prime 41 := by (______)
  exact hp.(______)
```

<details>
<summary>💡 답 보기</summary>

```lean
example (m : Nat) (h : m ∣ 13) : m = 1 ∨ m = 13 := by
  have hp : Nat.Prime 13 := by norm_num
  exact hp.eq_one_or_self_of_dvd m h

example : 2 ≤ 41 := by
  have hp : Nat.Prime 41 := by norm_num
  exact hp.two_le
```

</details>

---

## 7D.4 **대수학의 기본 정리**(Fundamental Theorem of Arithmetic)

### 7D.4.1 정리의 내용 (Rosen 정리 1)

> **정리 1** (대수학의 기본 정리): 1보다 큰 모든 정수는 소수이거나, 둘 이상의 소수의 곱으로 **유일하게** 표현할 수 있다. (소인수들은 점점 커지는 순서대로 나열할 수 있다.)

예를 들면:
- 100 = 2 · 2 · 5 · 5 = 2² · 5²
- 641 = 641 (소수이므로 그 자체)
- 999 = 3 · 3 · 3 · 37 = 3³ · 37
- 1024 = 2¹⁰

이 정리에는 두 가지 핵심이 있다:
1. **존재성**: 모든 수를 소수의 곱으로 쓸 수 있다
2. **유일성**: 그 방법이 (순서를 무시하면) 오직 하나뿐이다

### 7D.4.2 Lean4에서 소인수분해: `Nat.primeFactorsList`

Lean4의 Mathlib에는 소인수분해를 위한 함수가 있다:

```lean
-- 소인수 목록을 반환하는 함수
#check Nat.primeFactorsList
-- Nat.primeFactorsList : Nat → List Nat

-- 소인수 목록의 모든 원소는 소수
#check Nat.prime_of_mem_primeFactorsList
-- n.primeFactorsList의 원소 p → Nat.Prime p

-- 소인수 목록의 곱은 원래 수
#check Nat.prod_primeFactorsList
-- 0 < n → n.primeFactorsList.prod = n

-- 유일성
#check Nat.primeFactorsList_unique
```

실제로 소인수분해를 계산해 보자:

```lean
-- 구체적인 수의 소인수분해 확인
#eval Nat.primeFactorsList 100    -- [2, 2, 5, 5]
#eval Nat.primeFactorsList 641    -- [641]
#eval Nat.primeFactorsList 999    -- [3, 3, 3, 37]
#eval Nat.primeFactorsList 1024   -- [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
#eval Nat.primeFactorsList 7007   -- [7, 7, 11, 13]
#eval Nat.primeFactorsList 1     -- []  (1은 소인수가 없다)
```

### 7D.4.3 `Nat.factorization` — 소인수의 지수를 알려주는 함수

`Nat.primeFactorsList`가 목록을 반환하는 반면, `Nat.factorization`은 각 소인수의 **지수**(거듭제곱 횟수)를 함수로 반환한다:

```lean
-- n.factorization p = p가 n의 소인수분해에서 나타나는 횟수
#eval Nat.factorization 100 2   -- 2  (100 = 2² × 5²에서 2의 지수)
#eval Nat.factorization 100 5   -- 2  (100 = 2² × 5²에서 5의 지수)
#eval Nat.factorization 100 3   -- 0  (3은 100의 소인수가 아님)

#eval Nat.factorization 7007 7   -- 2  (7007 = 7² × 11 × 13)
#eval Nat.factorization 7007 11  -- 1
#eval Nat.factorization 7007 13  -- 1
```

### 연습 7D.3: 소인수분해 확인 (Rosen 예제 2, 4)

```lean
-- 연습 1: 교재 예제 2 — 소인수분해 확인
-- 100 = 2² × 5²
example : Nat.primeFactorsList 100 = [2, 2, 5, 5] := by native_decide

-- 641은 소수
example : Nat.primeFactorsList 641 = [641] := by native_decide

-- 999 = 3³ × 37
example : Nat.primeFactorsList 999 = sorry := by native_decide

-- 1024 = 2¹⁰
example : Nat.factorization 1024 2 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : Nat.primeFactorsList 999 = [3, 3, 3, 37] := by native_decide
example : Nat.factorization 1024 2 = 10 := by native_decide
```

</details>

```lean
-- 연습 2: 교재 예제 4 — 7007의 소인수분해
-- 7007 = 7 × 1001 = 7 × 7 × 143 = 7 × 7 × 11 × 13 = 7² × 11 × 13
example : Nat.primeFactorsList 7007 = sorry := by native_decide
example : Nat.factorization 7007 7 = sorry := by native_decide
example : Nat.factorization 7007 11 = sorry := by native_decide
example : Nat.factorization 7007 13 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : Nat.primeFactorsList 7007 = [7, 7, 11, 13] := by native_decide
example : Nat.factorization 7007 7 = 2 := by native_decide
example : Nat.factorization 7007 11 = 1 := by native_decide
example : Nat.factorization 7007 13 = 1 := by native_decide
```

**7007의 소인수분해 과정** (교재 예제 4와 동일):
1. 2, 3, 5는 7007의 약수가 아니다
2. 7 | 7007 → 7007 / 7 = 1001
3. 7 | 1001 → 1001 / 7 = 143
4. 7 ∤ 143, 11 | 143 → 143 / 11 = 13
5. 13은 소수이므로 완료
6. 결과: 7007 = 7 × 7 × 11 × 13 = 7² × 11 × 13

</details>

---

## 7D.5 **직접 나누어 보기**(Trial Division)로 소수 판정하기

### 7D.5.1 핵심 아이디어 (Rosen 정리 2)

> **정리 2**: 만약 n이 합성수라면, n의 소인수 중 하나는 √n보다 같거나 작다.

**증명 아이디어**: n이 합성수이면 n = ab로 쓸 수 있다 (1 < a, b < n). 만약 a > √n이고 b > √n이면 ab > n이 되어 모순이다. 따라서 a ≤ √n이거나 b ≤ √n이다.

**이 정리의 활용**: n이 소수인지 확인하려면, √n 이하의 모든 소수로 나누어 보면 된다. 하나라도 나누어떨어지면 합성수, 모두 나누어떨어지지 않으면 소수이다.

### 7D.5.2 직접 나누어 보기를 Lean4로 구현

```lean
-- 간단한 소수 판정 함수 (직접 나누어 보기)
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else
    -- 2부터 √n까지 나누어 본다
    let limit := n.sqrt
    let rec check (d : Nat) : Bool :=
      if d > limit then true        -- 더 이상 확인할 필요 없음 → 소수
      else if n % d == 0 then false  -- d로 나누어떨어짐 → 합성수
      else check (d + 1)             -- 다음 수로 확인
    check 2

-- 테스트
#eval isPrime 2     -- true
#eval isPrime 17    -- true
#eval isPrime 101   -- true
#eval isPrime 4     -- false
#eval isPrime 100   -- false
```

### 7D.5.3 교재 예제 3 — 101이 소수임을 보여라

√101 ≈ 10.05이므로, 10 이하의 소수 2, 3, 5, 7로 나누어 보면 된다.

```lean
-- 101은 2, 3, 5, 7 어느 것으로도 나누어떨어지지 않는다
example : 101 % 2 ≠ 0 := by norm_num
example : 101 % 3 ≠ 0 := by norm_num
example : 101 % 5 ≠ 0 := by norm_num
example : 101 % 7 ≠ 0 := by norm_num

-- 따라서 101은 소수이다
example : Nat.Prime 101 := by norm_num
```

### 연습 7D.4: 직접 나누어 보기 (Rosen 연습문제 1-2 유형)

다음 수가 소수인지 아닌지 판정하시오. 합성수라면 어떤 소수로 나누어떨어지는지 보이시오.

```lean
-- (a) 21: 합성수인지 확인
example : 21 % 3 = sorry := by norm_num   -- 3으로 나누어떨어짐
example : ¬ Nat.Prime 21 := by norm_num

-- (b) 29: 소수인지 확인 (√29 ≈ 5.38, 2,3,5로 나누어 봄)
example : 29 % 2 ≠ 0 := by norm_num
example : 29 % 3 ≠ 0 := by norm_num
example : 29 % 5 ≠ 0 := by norm_num
example : Nat.Prime 29 := by (______)

-- (c) 71: 소수인지 확인
example : Nat.Prime 71 := by (______)

-- (d) 97: 소수인지 확인
example : Nat.Prime 97 := by (______)

-- (e) 111: 합성수 — 어떤 소수로 나누어떨어지는가?
example : 111 % (______) = 0 := by norm_num
example : ¬ Nat.Prime 111 := by norm_num

-- (f) 143: 합성수 — 어떤 소수로 나누어떨어지는가?
example : 143 % (______) = 0 := by norm_num
example : ¬ Nat.Prime 143 := by norm_num
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (a) 21 = 3 × 7
example : 21 % 3 = 0 := by norm_num

-- (b) 29는 소수
example : Nat.Prime 29 := by norm_num

-- (c) 71은 소수
example : Nat.Prime 71 := by norm_num

-- (d) 97은 소수
example : Nat.Prime 97 := by norm_num

-- (e) 111 = 3 × 37
example : 111 % 3 = 0 := by norm_num

-- (f) 143 = 11 × 13
example : 143 % 11 = 0 := by norm_num
```

</details>

---

## 7D.6 **에라토스테네스의 체**(Sieve of Eratosthenes)

### 7D.6.1 알고리즘 설명

**에라토스테네스의 체**는 특정 수 이하의 소수를 모두 찾는 방법이다.

1. 2부터 n까지 모든 수를 나열한다
2. 2를 남기고, 2의 배수(4, 6, 8, ...)를 모두 지운다
3. 3을 남기고, 3의 배수(6, 9, 12, ...)를 모두 지운다
4. 5를 남기고, 5의 배수를 모두 지운다
5. 7을 남기고, 7의 배수를 모두 지운다
6. √n 이하의 소수까지 반복하면 완료

남아있는 수가 모두 소수이다.

### 7D.6.2 Lean4로 구현

```lean
-- 에라토스테네스의 체
def sieve (n : Nat) : List Nat :=
  let candidates := (List.range (n + 1)).drop 2  -- [2, 3, ..., n]
  candidates.filter fun c =>
    -- c의 약수가 2부터 √c까지 없으면 소수
    !(candidates.any fun d => d > 1 && d < c && c % d == 0)

-- 100 이하의 소수
#eval sieve 100
-- [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
--  53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
```

### 연습 7D.5: 에라토스테네스의 체 확인

```lean
-- 30 이하의 소수가 정확한지 확인
#eval sieve 30
-- 예상 결과: [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

-- 50 이하의 소수 개수
#eval (sieve 50).length  -- sorry (직접 확인)
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval (sieve 50).length  -- 15
-- 50 이하의 소수: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47
```

</details>

---

## 7D.7 **소수의 무한함**(Infinitely Many Primes)

### 7D.7.1 정리 (Rosen 정리 3)

> **정리 3**: 소수는 무한히 많다.

이것은 기원전 300년경 유클리드의 《원론》에 나오는 증명으로, 수학에서 가장 아름다운 증명 중 하나로 꼽힌다.

### 7D.7.2 증명 아이디어 (귀류법)

1. **가정**: 소수가 유한하다고 하자. 모든 소수가 p₁, p₂, ..., pₙ이라 하자.
2. Q = p₁ · p₂ · ... · pₙ + 1을 생각하자.
3. Q는 2 이상이므로, 대수학의 기본 정리에 의해 소인수를 가진다.
4. 그런데 Q를 어떤 pᵢ로 나누면 나머지가 항상 1이다 (왜냐하면 Q - p₁·p₂·...·pₙ = 1이므로).
5. 따라서 어떤 pᵢ도 Q를 나누지 못한다.
6. 이는 "모든 소수를 나열했다"는 가정에 모순이다.
7. 따라서 소수는 무한히 많다.

### 7D.7.3 Lean4에서 소수의 무한함 증명 — 단계별

이 증명은 『Mathematics in Lean』 5.3절에 자세히 나와 있다. 단계별로 살펴보자.

**1단계: 보조 정리 — "2 이상의 수는 소인수를 가진다"**

```lean
-- Mathlib에 이미 있는 정리
#check Nat.exists_prime_and_dvd
-- {n : Nat} → n ≠ 1 → ∃ p, Nat.Prime p ∧ p ∣ n
```

이 보조정리는 "1이 아닌 모든 자연수는 소인수를 가진다"고 말한다. 이것이 주요 정리의 핵심 도구이다.

**2단계: 핵심 관찰 — "p | n!이면 p ≤ n"**

```lean
-- 팩토리얼의 성질
#check Nat.factorial_pos  -- 0 < n!
#check Nat.dvd_factorial  -- 0 < p → (p ∣ n! ↔ p ≤ n)
```

`Nat.dvd_factorial`은 "양의 정수 p가 n!을 나누는 것 ↔ p ≤ n"이라는 ↔ 정리이다!

**3단계: 증명 전체 (간략 버전)**

```lean
-- 소수는 무한히 많다: 모든 n에 대해 n보다 큰 소수가 존재한다
theorem primes_infinite_sketch : ∀ n : Nat, ∃ p, p > n ∧ Nat.Prime p := by
  intro n
  -- Q = n! + 1을 생각한다
  have hQ : 2 ≤ Nat.factorial n + 1 := by
    have := Nat.factorial_pos n
    omega
  -- Q는 1이 아니므로 소인수 p를 가진다
  have hne1 : Nat.factorial n + 1 ≠ 1 := by omega
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne1
  -- p가 n보다 큼을 보인다
  refine ⟨p, ?_, hp⟩
  by_contra hle
  push_neg at hle  -- hle : p ≤ n
  -- p ≤ n이면 p | n! (팩토리얼의 성질)
  have hdvd_fact : p ∣ Nat.factorial n := by
    rw [Nat.dvd_factorial (by omega : 0 < p)]
    exact hle
  -- p | n! + 1이고 p | n!이면 p | 1
  have : p ∣ 1 := by
    have := Nat.dvd_sub' hdvd hdvd_fact
    simp at this
    exact this
  -- 그런데 소수는 2 이상이므로 p | 1은 불가능
  have : 2 ≤ p := hp.two_le
  omega
```

### 7D.7.4 증명을 한 줄 한 줄 분석

위 증명의 각 줄이 무엇을 하는지 아주 자세히 분석해 보자:

| 줄 | 코드 | 의미 |
|---|------|------|
| 1 | `intro n` | "임의의 자연수 n을 고정한다" |
| 2 | `have hQ : 2 ≤ n! + 1` | "n! + 1은 2 이상이다" (팩토리얼은 양수) |
| 3 | `have hne1 : n! + 1 ≠ 1` | "n! + 1은 1이 아니다" |
| 4 | `obtain ⟨p, hp, hdvd⟩` | "소인수 p를 꺼낸다" (존재 명제 분해) |
| 5 | `refine ⟨p, ?_, hp⟩` | "이 p가 답임을 제시하되, p > n은 아직 증명 안 함" |
| 6 | `by_contra hle` | "p ≤ n이라 가정하고 모순을 유도" |
| 7 | `hdvd_fact : p ∣ n!` | "p ≤ n이면 p가 n!을 나눈다" |
| 8 | `p ∣ 1` | "p | (n!+1)이고 p | n!이면 p | 1" |
| 9 | `omega` | "2 ≤ p인데 p | 1이면 모순!" |

### 연습 7D.6: 소수의 무한함 증명 이해하기

다음 증명의 빈칸을 채우시오:

```lean
-- 보조 정리: n! + 1의 소인수는 n보다 크다
lemma prime_factor_of_factorial_succ (n : Nat)
  (p : Nat) (hp : Nat.Prime p) (hdvd : p ∣ Nat.factorial n + 1) :
  p > n := by
  by_contra hle
  push_neg at hle
  have h1 : p ∣ Nat.factorial n := by
    rw [(______)]
    exact hle
  have h2 : p ∣ 1 := by
    have := Nat.dvd_sub' hdvd h1
    (______)
  have h3 : 2 ≤ p := hp.(______)
  omega
```

<details>
<summary>💡 답 보기</summary>

```lean
lemma prime_factor_of_factorial_succ (n : Nat)
  (p : Nat) (hp : Nat.Prime p) (hdvd : p ∣ Nat.factorial n + 1) :
  p > n := by
  by_contra hle
  push_neg at hle
  have h1 : p ∣ Nat.factorial n := by
    rw [Nat.dvd_factorial (by omega : 0 < p)]
    exact hle
  have h2 : p ∣ 1 := by
    have := Nat.dvd_sub' hdvd h1
    simp at this
    exact this
  have h3 : 2 ≤ p := hp.two_le
  omega
```

</details>

---

## 7D.8 **메르센 소수**(Mersenne Primes)

### 7D.8.1 정의

2ⁿ − 1 형태의 소수를 **메르센 소수**라 한다. n이 소수가 아니면 2ⁿ − 1도 소수가 될 수 없다 (연습문제 참조).

### 7D.8.2 교재 예제 5 확인

```lean
-- 교재 예제 5: 메르센 수 확인
-- 2² − 1 = 3: 소수
example : 2^2 - 1 = 3 := by norm_num
example : Nat.Prime (2^2 - 1) := by norm_num

-- 2³ − 1 = 7: 소수
example : 2^3 - 1 = 7 := by norm_num
example : Nat.Prime (2^3 - 1) := by norm_num

-- 2⁵ − 1 = 31: 소수
example : 2^5 - 1 = 31 := by norm_num
example : Nat.Prime (2^5 - 1) := by norm_num

-- 2⁷ − 1 = 127: 소수
example : 2^7 - 1 = 127 := by norm_num
example : Nat.Prime (2^7 - 1) := by norm_num

-- 2¹¹ − 1 = 2047 = 23 × 89: 소수가 아님!
example : 2^11 - 1 = 2047 := by norm_num
example : ¬ Nat.Prime (2^11 - 1) := by norm_num
```

### 연습 7D.7: 메르센 수 (sorry 식)

```lean
-- 2⁴ − 1 = 15: 소수인가?
example : 2^4 - 1 = 15 := by norm_num
example : Nat.Prime (2^4 - 1) ∨ ¬ Nat.Prime (2^4 - 1) := by
  sorry

-- 2¹³ − 1 = 8191: 소수인가?
example : 2^13 - 1 = 8191 := by norm_num
example : Nat.Prime (2^13 - 1) ∨ ¬ Nat.Prime (2^13 - 1) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 15 = 3 × 5: 소수가 아님
example : Nat.Prime (2^4 - 1) ∨ ¬ Nat.Prime (2^4 - 1) := by
  right; norm_num

-- 8191: 소수!
example : Nat.Prime (2^13 - 1) ∨ ¬ Nat.Prime (2^13 - 1) := by
  left; norm_num
```

</details>

---

## 7D.9 **서로소**(Coprime)와 **소수의 곱 성질**

### 7D.9.1 서로소의 정의

두 자연수 a와 b의 최대공약수가 1이면, a와 b는 **서로소**(coprime, relatively prime)라 한다.

```lean
-- Lean4에서 서로소
#check Nat.Coprime
-- Nat.Coprime m n은 Nat.gcd m n = 1과 같다

example : Nat.Coprime 12 7 := by norm_num   -- gcd(12, 7) = 1
example : Nat.Coprime 17 22 := by norm_num  -- gcd(17, 22) = 1
example : ¬ Nat.Coprime 12 8 := by norm_num -- gcd(12, 8) = 4 ≠ 1
```

### 7D.9.2 소수와 서로소의 관계

p가 소수이면, p | n이 아닌 한 p와 n은 서로소이다:

```lean
-- p가 소수이고 p ∤ n이면, gcd(p, n) = 1
#check Nat.Prime.coprime_iff_not_dvd
-- Nat.Prime.coprime_iff_not_dvd :
--   Nat.Prime p → (Nat.Coprime p n ↔ ¬ p ∣ n)
```

이것은 ↔ 정리이다! "p가 소수일 때, p와 n이 서로소 ↔ p가 n을 나누지 않는다."

### 연습 7D.8: 서로소 확인

```lean
-- 연습 1: 기본 서로소 확인
example : Nat.Coprime 10 21 := by (______)
example : Nat.Coprime 35 44 := by (______)

-- 연습 2: 서로소가 아닌 경우
example : ¬ Nat.Coprime 10 15 := by (______)

-- 연습 3: 7은 소수이므로, 7 ∤ 10이면 gcd(7, 10) = 1
example : Nat.Coprime 7 10 := by (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
example : Nat.Coprime 10 21 := by norm_num
example : Nat.Coprime 35 44 := by norm_num

example : ¬ Nat.Coprime 10 15 := by norm_num  -- gcd(10, 15) = 5

example : Nat.Coprime 7 10 := by norm_num
```

</details>

---

## 7D.10 연습문제 세트: 소수 종합 (sorry 식)

### 연습 7D.9: Rosen 연습문제 1 유형

다음 수가 소수인지 아닌지 판정하시오.

```lean
-- (a) 19
theorem ex_1a : Nat.Prime 19 := by sorry

-- (b) 27
theorem ex_1b : ¬ Nat.Prime 27 := by sorry

-- (c) 93
theorem ex_1c : ¬ Nat.Prime 93 := by sorry

-- (d) 101
theorem ex_1d : Nat.Prime 101 := by sorry

-- (e) 107
theorem ex_1e : Nat.Prime 107 := by sorry

-- (f) 113
theorem ex_1f : Nat.Prime 113 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex_1a : Nat.Prime 19 := by norm_num
theorem ex_1b : ¬ Nat.Prime 27 := by norm_num   -- 27 = 3³
theorem ex_1c : ¬ Nat.Prime 93 := by norm_num   -- 93 = 3 × 31
theorem ex_1d : Nat.Prime 101 := by norm_num
theorem ex_1e : Nat.Prime 107 := by norm_num
theorem ex_1f : Nat.Prime 113 := by norm_num
```

</details>

### 연습 7D.10: Rosen 연습문제 3-4 유형 — 소인수분해

```lean
-- (a) 88의 소인수분해
example : Nat.primeFactorsList 88 = sorry := by native_decide

-- (b) 126의 소인수분해
example : Nat.primeFactorsList 126 = sorry := by native_decide

-- (c) 729의 소인수분해
example : Nat.primeFactorsList 729 = sorry := by native_decide

-- (d) 1001의 소인수분해
example : Nat.primeFactorsList 1001 = sorry := by native_decide

-- (e) 1111의 소인수분해
example : Nat.primeFactorsList 1111 = sorry := by native_decide

-- (f) 909090의 소인수분해
-- 힌트: #eval Nat.primeFactorsList 909090
example : Nat.primeFactorsList 909090 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (a) 88 = 2³ × 11
example : Nat.primeFactorsList 88 = [2, 2, 2, 11] := by native_decide

-- (b) 126 = 2 × 3² × 7
example : Nat.primeFactorsList 126 = [2, 3, 3, 7] := by native_decide

-- (c) 729 = 3⁶
example : Nat.primeFactorsList 729 = [3, 3, 3, 3, 3, 3] := by native_decide

-- (d) 1001 = 7 × 11 × 13
example : Nat.primeFactorsList 1001 = [7, 11, 13] := by native_decide

-- (e) 1111 = 11 × 101
example : Nat.primeFactorsList 1111 = [11, 101] := by native_decide

-- (f) 909090 = 2 × 3 × 5 × 7 × 11 × 13 × 61
-- 놀랍게도 작은 소수들의 곱에 61이 하나 붙는다!
-- 확인: #eval Nat.primeFactorsList 909090
example : Nat.primeFactorsList 909090 = [2, 3, 3, 5, 10101] := by native_decide
-- 주의: 909090 = 2 × 3² × 5 × 10101, 그리고 10101 = 3 × 7 × 13 × 37
-- 실제로는 #eval로 확인하는 것이 가장 정확하다
```

</details>

### 연습 7D.11: 메르센 수 판정 (Rosen 연습문제 20 유형)

```lean
-- (a) 2⁷ − 1은 소수인가?
theorem mersenne_7 : Nat.Prime (2^7 - 1) := by sorry

-- (b) 2⁹ − 1은 소수인가?
-- 힌트: 2⁹ − 1 = 511
theorem mersenne_9 : ¬ Nat.Prime (2^9 - 1) := by sorry

-- (c) 2¹¹ − 1은 소수인가?
theorem mersenne_11 : ¬ Nat.Prime (2^11 - 1) := by sorry

-- (d) 2¹³ − 1은 소수인가?
theorem mersenne_13 : Nat.Prime (2^13 - 1) := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (a) 2⁷ − 1 = 127: 소수!
theorem mersenne_7 : Nat.Prime (2^7 - 1) := by norm_num

-- (b) 2⁹ − 1 = 511 = 7 × 73: 합성수
theorem mersenne_9 : ¬ Nat.Prime (2^9 - 1) := by norm_num

-- (c) 2¹¹ − 1 = 2047 = 23 × 89: 합성수
theorem mersenne_11 : ¬ Nat.Prime (2^11 - 1) := by norm_num

-- (d) 2¹³ − 1 = 8191: 소수!
theorem mersenne_13 : Nat.Prime (2^13 - 1) := by norm_num
```

**규칙**: 2ⁿ − 1이 소수가 되려면, n 자체도 소수여야 한다. 하지만 n이 소수라고 해서 2ⁿ − 1이 반드시 소수는 아니다 (n = 11이 반례).

</details>

---

## 7D.11 전술 및 라이브러리 정리 요약

### 이 장에서 새로 배운 전술 & 함수

| 이름 | 용도 | 예시 |
|------|------|------|
| `Nat.Prime` | 소수 판정 타입 | `Nat.Prime 17` |
| `Nat.prime_two` | 2는 소수 | `Nat.prime_two : Nat.Prime 2` |
| `Nat.prime_three` | 3은 소수 | `Nat.prime_three : Nat.Prime 3` |
| `.eq_one_or_self_of_dvd` | 소수의 약수 성질 | `hp.eq_one_or_self_of_dvd m hm` |
| `.two_le` | 소수 ≥ 2 | `hp.two_le` |
| `.dvd_mul` | 소수가 곱을 나누면 | `hp.dvd_mul` |
| `Nat.primeFactorsList` | 소인수 목록 | `#eval Nat.primeFactorsList 100` |
| `Nat.factorization` | 소인수 지수 | `Nat.factorization 100 2 = 2` |
| `Nat.Coprime` | 서로소 판정 | `Nat.Coprime 12 7` |
| `Nat.factorial` | 팩토리얼 | `Nat.factorial 5 = 120` |
| `Nat.dvd_factorial` | p ∣ n! ↔ p ≤ n | 소수 무한 증명에 사용 |
| `Nat.dvd_sub'` | a ∣ b이고 a ∣ c이면 a ∣ b-c | 소수 무한 증명에 사용 |
| `native_decide` | 결정가능한 명제 자동 증명 | 리스트 등식 확인 |

### 이전 장 전술 (복습)

| 전술 | 최초 등장 | 용도 |
|------|---------|------|
| `norm_num` | Part 4 | 구체적 수치 계산 |
| `omega` | Part 4 | 자연수/정수 선형 산술 |
| `constructor` | Part 4 | ↔ 또는 ∧를 분리 |
| `obtain ⟨...⟩` | Part 7-A | 존재 명제 분해 |
| `by_contra` | Part 4-3 | 귀류법 |
| `push_neg` | Part 4-3 | 부정 안으로 밀어넣기 |
| `rw` | Part 4 | 치환(슈퍼포지션) |

---

## 다음 편(7-E) 예고

**제7-E편**에서는:
- **최대공약수**(greatest common divisor)와 **최소공배수**(least common multiple)
- **유클리드 알고리즘**(Euclidean algorithm) — gcd를 효율적으로 구하는 방법
- **베주의 정리**(Bézout's theorem) — gcd(a,b) = sa + tb
- **확장 유클리드 알고리즘**(extended Euclidean algorithm)

를 다룬다.

---

**(끝)**
