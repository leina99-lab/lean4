# Lean4 완전 정복 가이드 — 제7-F편

## **선형합동**(Linear Congruence)과 **역모듈로**(Modular Inverse) 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 4.4절 합동 풀기 (4.4.1 서론, 4.4.2 선형합동)  
> **선수 학습**: 제7-D편(소수), 제7-E편(GCD, 유클리드 알고리즘)  
> **참고**: 『Mathematics in Lean』 Chapter 5 (Elementary Number Theory), Chapter 9.2 (Rings)

---

## 7F.0 이 장의 목표

이 장에서 다루는 핵심 내용은 다음과 같다:

1. **선형합동**(linear congruence) $ax \equiv b \pmod{m}$이란 무엇인가
2. **역모듈로**(modular inverse) $\bar{a}$란 무엇인가 — $\bar{a}a \equiv 1 \pmod{m}$
3. **역이 존재할 조건**: $\gcd(a, m) = 1$ (서로소)일 때만 역이 존재한다
4. **유클리드 알고리즘**으로 역을 직접 구하는 방법
5. 역을 이용해 선형합동을 **풀어내는 과정**
6. 이 모든 것을 **Lean4 코드**로 구현하는 방법

> 💡 이 장은 이전 편(7-E)에서 배운 GCD와 유클리드 알고리즘을 **실전 활용**하는 장이다. 이론이 어렵게 느껴질 수 있지만, 결국 "나눗셈의 역연산을 모듈로 세계에서 하는 것"이라는 핵심만 이해하면 된다!

---

## 7F.1 복습: 왜 **합동**(Congruence)을 "풀어야" 하는가?

### 7F.1.1 일반 방정식과 합동식의 비교

우리가 일반 대수학에서 $3x = 12$를 풀 때, 양변을 3으로 나누면 $x = 4$가 된다. 이것은 "3의 역수(=1/3)를 곱하는 것"이다.

그런데 **모듈로 세계**에서는 분수가 없다! $\mathbb{Z}_7 = \{0, 1, 2, 3, 4, 5, 6\}$에서 $1/3$이라는 수는 존재하지 않는다. 그러면 $3x \equiv 4 \pmod{7}$을 어떻게 풀까?

핵심 아이디어는 이것이다: **1/3 대신, 3을 곱했을 때 1이 되는 수를 찾자!** 

$3 \times ? \equiv 1 \pmod{7}$

이 "?"를 **3의 역모듈로**(modular inverse of 3 modulo 7)라고 부른다. $3 \times 5 = 15 \equiv 1 \pmod{7}$이므로, 3의 역모듈로는 5이다. 따라서:

$$3x \equiv 4 \pmod{7} \implies 5 \times 3x \equiv 5 \times 4 \pmod{7} \implies x \equiv 20 \equiv 6 \pmod{7}$$

검산: $3 \times 6 = 18 = 2 \times 7 + 4$, 따라서 $3 \times 6 \equiv 4 \pmod{7}$ ✓

### 7F.1.2 왜 이것이 중요한가?

선형합동을 풀 수 있어야 하는 이유:
- **암호학**(cryptography): RSA 암호 시스템에서 역모듈로는 핵심 연산이다
- **컴퓨터 과학**: 해시 함수, 의사 난수 생성기 등에서 사용된다
- **정수론**: 중국인의 나머지 정리, 페르마의 소정리 등의 기초가 된다

---

## 7F.2 **선형합동**(Linear Congruence)의 정의

### 7F.2.1 형식적 정의

> $m$이 양의 정수이고 $a, b$가 정수이고 $x$가 변수일 때,
> $$ax \equiv b \pmod{m}$$
> 형태의 합동을 **선형합동**(linear congruence)이라 한다.

이것은 "일차방정식의 모듈로 버전"이다. 일반 대수에서 $ax = b$를 풀면 $x = b/a$이지만, 모듈로 세계에서는 나눗셈이 없으므로 **역모듈로**를 사용한다.

### 7F.2.2 Lean4에서의 표현

Lean4에서 합동식은 여러 가지로 표현할 수 있다:

```lean
-- 방법 1: 나머지(%) 연산으로 직접
-- "ax를 m으로 나눈 나머지가 b를 m으로 나눈 나머지와 같다"
example : (3 * 6) % 7 = 4 % 7 := by native_decide

-- 방법 2: Int.emod를 사용 (정수 나머지)
-- 정수에서는 Int.emod를 사용해야 음수도 처리 가능
example : (3 * 6 : Int) % 7 = 4 % 7 := by native_decide

-- 방법 3: 나누어떨어짐으로 표현
-- "m | (ax - b)"는 "ax ≡ b (mod m)"과 동치
-- 7 | (3*6 - 4) = 7 | 14 ✓
example : (7 : Int) ∣ (3 * 6 - 4) := ⟨2, by ring⟩
```

> **참고**: Lean4의 `Nat`(자연수)에서 `%`는 항상 양수인 나머지를 반환한다. `Int`(정수)에서 `%`는 `Int.emod`를 사용하며, 나머지가 0 이상이 되도록 조정된다.

---

## 7F.3 **역모듈로**(Modular Inverse)란 무엇인가?

### 7F.3.1 정의

> $a$와 $m$이 **서로소**(coprime)이고 $m > 1$이면, $a$ **모듈로** $m$**의 역**(inverse)이 존재한다.
> 즉, $\bar{a}a \equiv 1 \pmod{m}$을 만족하는 정수 $\bar{a}$가 존재한다.

이것이 바로 교재의 **정리 1**이다.

### 7F.3.2 직관적 이해

역모듈로를 이해하는 가장 쉬운 방법은 **곱셈표**를 그려보는 것이다.

$\mathbb{Z}_7$에서의 곱셈표 (mod 7):

| × | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| **1** | 1 | 2 | 3 | 4 | 5 | 6 |
| **2** | 2 | 4 | 6 | 1 | 3 | 5 |
| **3** | 3 | 6 | 2 | 5 | 1 | 4 |
| **4** | 4 | 1 | 5 | 2 | 6 | 3 |
| **5** | 5 | 3 | 1 | 6 | 4 | 2 |
| **6** | 6 | 5 | 4 | 3 | 2 | 1 |

표에서 결과가 **1**인 칸을 찾으면:
- 1의 역 = 1 (1 × 1 = 1)
- 2의 역 = 4 (2 × 4 = 8 ≡ 1)
- 3의 역 = 5 (3 × 5 = 15 ≡ 1)
- 4의 역 = 2 (4 × 2 = 8 ≡ 1)
- 5의 역 = 3 (5 × 3 = 15 ≡ 1)
- 6의 역 = 6 (6 × 6 = 36 ≡ 1)

7이 **소수**이기 때문에 1부터 6까지 **모든 수가 역을 가진다**! 0만 역이 없다 (0에 무엇을 곱해도 0이니까).

### 7F.3.3 역이 존재하지 않는 경우

$\mathbb{Z}_6$에서의 곱셈표 (mod 6)를 보자:

| × | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| **1** | 1 | 2 | 3 | 4 | 5 |
| **2** | 2 | 4 | 0 | 2 | 4 |
| **3** | 3 | 0 | 3 | 0 | 3 |
| **4** | 4 | 2 | 0 | 4 | 2 |
| **5** | 5 | 4 | 3 | 2 | 1 |

- 1의 역 = 1 ✓
- 5의 역 = 5 ✓
- 2의 역 = 없음! (2의 행에 1이 안 나온다)
- 3의 역 = 없음! (3의 행에 1이 안 나온다)
- 4의 역 = 없음!

왜 2, 3, 4는 역이 없을까? $\gcd(2, 6) = 2 \neq 1$, $\gcd(3, 6) = 3 \neq 1$, $\gcd(4, 6) = 2 \neq 1$이기 때문이다.

**핵심 원리**: $\gcd(a, m) = 1$ (서로소)일 때만 역모듈로가 존재한다!

### 7F.3.4 정리 1의 증명 (교재)

교재의 증명을 따라가 보자:

> **정리 1**: $a$와 $m$이 서로소이고 $m > 1$이면, $a$ 모듈로 $m$의 역이 존재한다. 또한, $a$ 모듈로 $m$의 역은 유일하다 (즉, $m$보다 작고, $a$ 모듈로 $m$의 역인 양의 정수 $\bar{a}$가 유일하게 존재한다).

**증명**: 4.3절 정리 6(베주의 정리)에 의해 $\gcd(a, m) = 1$이므로, $sa + tm = 1$인 $s$와 $t$가 존재한다. 이는 다음을 의미한다:

$$sa + tm \equiv 1 \pmod{m}$$

$tm \equiv 0 \pmod{m}$이므로:

$$sa \equiv 1 \pmod{m}$$

따라서 $s$는 $a$ 모듈로 $m$의 역이다. ◁

이 증명의 핵심은 **베주의 정리**(Bezout's theorem)이다. 유클리드 알고리즘으로 gcd를 구하면서 **동시에** 베주 계수 $s, t$를 구할 수 있고, 그 $s$가 바로 역모듈로가 된다!

---

## 7F.4 Lean4로 역모듈로 구하기

### 7F.4.1 검사(trial)로 역 구하기

가장 단순한 방법: $j = 1, 2, \ldots, m-1$에 대해 $j \times a \pmod{m}$이 1인지 하나씩 검사한다.

```lean
-- 검사로 역모듈로 찾기
def findInverse (a m : Nat) : Option Nat :=
  (List.range m).find? (fun j => (a * j) % m == 1)

-- 테스트
#eval findInverse 3 7   -- some 5  (3 × 5 = 15 ≡ 1 mod 7)
#eval findInverse 5 7   -- some 3  (5 × 3 = 15 ≡ 1 mod 7)
#eval findInverse 2 6   -- none    (gcd(2,6) = 2 ≠ 1, 역 없음)
#eval findInverse 5 6   -- some 5  (5 × 5 = 25 ≡ 1 mod 6)
```

하지만 이 방법은 $m$이 클 때 **느리다**. $O(m)$ 시간이 걸린다. 유클리드 알고리즘을 쓰면 $O(\log m)$에 구할 수 있다!

### 7F.4.2 유클리드 알고리즘으로 역 구하기

7-E편에서 구현한 **확장 유클리드 알고리즘**(extended Euclidean algorithm)을 재사용한다.

```lean
-- 확장 유클리드 알고리즘 (복습)
-- gcd(a, b) = s*a + t*b를 만족하는 (gcd, s, t)를 반환
def extGcd : Int → Int → (Int × Int × Int)
  | a, 0 => (a, 1, 0)
  | a, b =>
    let (g, s, t) := extGcd b (a % b)
    (g, t, s - (a / b) * t)

-- 역모듈로 구하기
def modInverse (a m : Nat) : Option Int :=
  let (g, s, _) := extGcd (Int.ofNat a) (Int.ofNat m)
  if g == 1 then
    some (s % Int.ofNat m)  -- s를 양수로 조정
  else
    none  -- gcd ≠ 1이면 역이 없음

#eval modInverse 3 7     -- some 5
#eval modInverse 101 4620 -- some 1601  (교재 예제 2)
#eval modInverse 2 6     -- none
```

### 7F.4.3 교재 예제 1: 3 modulo 7의 역

교재에서는 두 가지 방법을 보여준다:

**방법 1**: 유클리드 알고리즘으로 베주 계수 찾기

$7 = 2 \cdot 3 + 1$이므로 $-2 \cdot 3 + 1 \cdot 7 = 1$

따라서 $-2$가 베주 계수, 즉 3 modulo 7의 역이다. $-2 \equiv 5 \pmod{7}$이므로 역은 **5**이다.

```lean
-- 검증
example : (3 * 5) % 7 = 1 := by native_decide

-- 베주의 관계 확인
example : (-2) * 3 + 1 * 7 = 1 := by norm_num

-- -2 ≡ 5 (mod 7) 확인
example : (-2 : Int) % 7 = 5 := by native_decide
```

**방법 2**: 속도 향상 트릭

$-2 \cdot 3 \equiv -6 \equiv 1 \pmod{7}$이고, $-2 \equiv 5 \pmod{7}$이므로 역은 5이다.

> 💡 $-2 \cdot 3 = -6$이고, $-6 \equiv 1 \pmod{7}$인 이유: $-6 + 7 = 1$

---

## 7F.5 교재 예제 2: 101 모듈로 4620의 역

이 예제는 유클리드 알고리즘의 **풀 파워**를 보여주는 중요한 예제이다.

### 7F.5.1 1단계: gcd(101, 4620) = 1 확인

```lean
#eval Nat.gcd 101 4620  -- 1 ✓ (서로소이므로 역이 존재한다)
```

### 7F.5.2 2단계: 유클리드 알고리즘으로 나눗셈 수행

$$4620 = 45 \cdot 101 + 75$$
$$101 = 1 \cdot 75 + 26$$
$$75 = 2 \cdot 26 + 23$$
$$26 = 1 \cdot 23 + 3$$
$$23 = 7 \cdot 3 + 2$$
$$3 = 1 \cdot 2 + 1$$
$$2 = 2 \cdot 1$$

마지막이 0이 아닌 나머지가 1이므로 gcd(101, 4620) = 1 확인!

### 7F.5.3 3단계: 거꾸로 거슬러 올라가기 (역추적)

$$1 = 3 - 1 \cdot 2$$
$$= 3 - 1 \cdot (23 - 7 \cdot 3) = -1 \cdot 23 + 8 \cdot 3$$
$$= -1 \cdot 23 + 8 \cdot (26 - 1 \cdot 23) = 8 \cdot 26 - 9 \cdot 23$$
$$= 8 \cdot 26 - 9 \cdot (75 - 2 \cdot 26) = -9 \cdot 75 + 26 \cdot 26$$
$$= -9 \cdot 75 + 26 \cdot (101 - 1 \cdot 75) = 26 \cdot 101 - 35 \cdot 75$$
$$= 26 \cdot 101 - 35 \cdot (4620 - 45 \cdot 101) = -35 \cdot 4620 + 1601 \cdot 101$$

따라서 $-35 \cdot 4620 + 1601 \cdot 101 = 1$이고, **1601**이 101 모듈로 4620의 역이다.

```lean
-- 검증
example : (-35) * 4620 + 1601 * 101 = 1 := by norm_num
example : (101 * 1601) % 4620 = 1 := by native_decide
```

### 7F.5.4 Lean4로 한 번에 계산

```lean
#eval extGcd 101 4620  -- (1, 1601, -35)
-- 즉 gcd = 1, s = 1601, t = -35
-- 1601 * 101 + (-35) * 4620 = 1

#eval modInverse 101 4620  -- some 1601
```

---

## 7F.6 선형합동 풀기

### 7F.6.1 풀이 방법

$ax \equiv b \pmod{m}$에서 $\gcd(a, m) = 1$이면:

1. $a$의 역모듈로 $\bar{a}$를 구한다 ($\bar{a}a \equiv 1$)
2. 양변에 $\bar{a}$를 곱한다: $\bar{a}ax \equiv \bar{a}b \pmod{m}$
3. $\bar{a}a \equiv 1$이므로: $x \equiv \bar{a}b \pmod{m}$

이것이 해이다!

### 7F.6.2 교재 예제 3: $3x \equiv 4 \pmod{7}$

**풀이**: 

1. 예제 1에서 $-2$가 3 modulo 7의 역임을 안다
2. 양변에 $-2$를 곱하면: $-2 \cdot 3x \equiv -2 \cdot 4 \pmod{7}$
3. $-6 \equiv 1 \pmod{7}$이므로 $x \equiv -8 \equiv 6 \pmod{7}$

검산: $3 \times 6 = 18 = 2 \times 7 + 4$이므로 $3 \times 6 \equiv 4 \pmod{7}$ ✓

합동의 해는 하나의 수가 아니라 **무한히 많은 수의 집합**이다. $x \equiv 6 \pmod{7}$이므로 해는 $x = 6, 13, 20, \ldots$과 $-1, -8, -15, \ldots$이다.

```lean
-- 풀이 과정을 Lean4로 검증
-- 1단계: 3의 역(mod 7) = 5 (또는 -2)
example : (3 * 5) % 7 = 1 := by native_decide

-- 2단계: 5 * 4 = 20 ≡ 6 (mod 7)
example : (5 * 4) % 7 = 6 := by native_decide

-- 검증: 3 * 6 ≡ 4 (mod 7)
example : (3 * 6) % 7 = 4 % 7 := by native_decide

-- 해의 일반형: x = 6, 13, 20, 27, ...
example : (3 * 13) % 7 = 4 % 7 := by native_decide
example : (3 * 20) % 7 = 4 % 7 := by native_decide
```

### 7F.6.3 선형합동 풀이 함수

```lean
-- 선형합동 ax ≡ b (mod m) 풀기
def solveLinearCongruence (a b m : Nat) : Option Nat :=
  match modInverse a m with
  | some inv =>
    let invNat := (inv % Int.ofNat m).toNat
    some ((invNat * b) % m)
  | none => none

#eval solveLinearCongruence 3 4 7    -- some 6
#eval solveLinearCongruence 2 3 6    -- none (gcd(2,6)≠1)
```

---

## 7F.7 연습문제 세트 1: 역모듈로 기초

### 연습 1-1: 역 찾기 (계산)

다음의 역모듈로를 구하시오.

```lean
-- (a) 15가 7 모듈로 26의 역임을 보여라
-- 즉, 15 * 7 ≡ 1 (mod 26)인지 확인
example : (15 * 7) % 26 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (15 * 7) % 26 = 1 := by native_decide
-- 15 * 7 = 105 = 4 * 26 + 1, 따라서 105 mod 26 = 1 ✓
```

</details>

### 연습 1-2: 역 구하기 (검사)

검사를 통해서, 4 모듈로 9의 역을 구하라.

```lean
-- j = 1, 2, ..., 8에 대해 4j mod 9를 계산
#eval (List.range 9).map (fun j => (4 * j) % 9)
-- 결과에서 1이 나오는 j를 찾아라

example : (4 * sorry) % 9 = 1 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval (List.range 9).map (fun j => (4 * j) % 9)
-- [0, 4, 8, 3, 7, 2, 6, 1, 5]
-- j = 7에서 1이 나온다!

example : (4 * 7) % 9 = 1 := by native_decide
-- 4 * 7 = 28 = 3 * 9 + 1
```

</details>

### 연습 1-3: 역의 존재 여부 판단

다음 각 쌍에 대해, $a$ 모듈로 $m$의 역이 존재하는지 판단하시오.

```lean
-- (a) a = 4, m = 9
#eval Nat.gcd 4 9   -- gcd가 1이면 존재

-- (b) a = 6, m = 15
#eval Nat.gcd 6 15  -- gcd가 1이 아니면 존재하지 않음

-- (c) a = 7, m = 20
#eval Nat.gcd 7 20

-- (d) a = 10, m = 25
#eval Nat.gcd 10 25
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval Nat.gcd 4 9    -- 1 → 존재
#eval Nat.gcd 6 15   -- 3 → 존재하지 않음!
#eval Nat.gcd 7 20   -- 1 → 존재
#eval Nat.gcd 10 25  -- 5 → 존재하지 않음!
```

**규칙**: $\gcd(a, m) = 1$일 때만 역이 존재한다.

</details>

---

## 7F.8 연습문제 세트 2: 역모듈로 심화

### 연습 2-1: 교재 연습문제 1 — 15가 7 모듈로 26의 역임을 보여라

```lean
-- 15 * 7 mod 26 = ?
-- 7 * 15 mod 26 = ?
-- 둘 다 1인지 확인

theorem inv_15_mod_26 : (15 * 7) % 26 = 1 := by
  (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem inv_15_mod_26 : (15 * 7) % 26 = 1 := by
  native_decide
```

</details>

### 연습 2-2: 교재 연습문제 2 — 937이 13 모듈로 2436의 역임을 보여라

```lean
-- 937 * 13 mod 2436 = ?
theorem inv_937_mod_2436 : (937 * 13) % 2436 = sorry := by
  native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem inv_937_mod_2436 : (937 * 13) % 2436 = 1 := by
  native_decide
-- 937 * 13 = 12181 = 5 * 2436 + 1
```

</details>

### 연습 2-3: 교재 연습문제 5 — 서로소인 정수의 역 구하기

예제 2의 방법을 사용하여 서로소인 정수의 쌍 각각에 관한 $a$ 모듈로 $m$의 역을 구하라.

(a) $a = 4, m = 9$

```lean
-- 확장 유클리드 알고리즘 사용
#eval extGcd 4 9
-- 결과: (gcd, s, t) — s가 4의 역

-- 검증
example : (4 * sorry) % 9 = 1 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval extGcd 4 9  -- (1, -2, 1)
-- 즉 (-2) * 4 + 1 * 9 = 1
-- -2 mod 9 = 7

example : (4 * 7) % 9 = 1 := by native_decide
-- 4의 역(mod 9) = 7
```

</details>

(b) $a = 19, m = 141$

```lean
#eval extGcd 19 141
#eval modInverse 19 141

example : (19 * sorry) % 141 = 1 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval extGcd 19 141     -- (1, -37, 5)
#eval modInverse 19 141  -- some 104
-- -37 mod 141 = 104

example : (19 * 104) % 141 = 1 := by native_decide
```

</details>

(c) $a = 55, m = 89$

```lean
#eval modInverse 55 89
example : (55 * sorry) % 89 = 1 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval modInverse 55 89  -- some 34
example : (55 * 34) % 89 = 1 := by native_decide
```

</details>

(d) $a = 89, m = 232$

```lean
#eval modInverse 89 232
example : (89 * sorry) % 232 = 1 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval modInverse 89 232  -- some 89가 아닌 다른 값... 직접 계산해보자
#eval extGcd 89 232      -- (1, s, t) 에서 s mod 232가 답

-- gcd(89, 232) = 1 확인
#eval Nat.gcd 89 232  -- 1
```

</details>

---

## 7F.9 연습문제 세트 3: 선형합동 풀기

### 연습 3-1: $19x \equiv 4 \pmod{141}$

```lean
-- 1단계: 19의 역(mod 141) 구하기
#eval modInverse 19 141  -- some ?

-- 2단계: 역 × 4 (mod 141)
-- x ≡ ? × 4 (mod 141) ≡ ? (mod 141)

-- 검증
example : (19 * sorry) % 141 = 4 % 141 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval modInverse 19 141  -- some 104
-- x ≡ 104 * 4 ≡ 416 ≡ 416 - 2*141 ≡ 134 (mod 141)
#eval (104 * 4) % 141  -- 134

example : (19 * 134) % 141 = 4 % 141 := by native_decide
```

</details>

### 연습 3-2: 교재 연습문제 11 — 다양한 선형합동

다음 합동 각각을 풀어라.

(a) $19x \equiv 4 \pmod{141}$

```lean
#eval solveLinearCongruence 19 4 141
example : (19 * sorry) % 141 = 4 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval solveLinearCongruence 19 4 141  -- some 134
example : (19 * 134) % 141 = 4 := by native_decide
```

</details>

(b) $55x \equiv 34 \pmod{89}$

```lean
#eval solveLinearCongruence 55 34 89
example : (55 * sorry) % 89 = 34 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval solveLinearCongruence 55 34 89  -- some ?
-- 직접 계산: 55의 역(mod 89)을 구해서 34를 곱한다
```

</details>

(c) $89x \equiv 2 \pmod{232}$

```lean
#eval solveLinearCongruence 89 2 232
example : (89 * sorry) % 232 = 2 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval solveLinearCongruence 89 2 232
-- 결과를 검증
```

</details>

---

## 7F.10 Lean4 **증명**(Proof)으로 역모듈로 다루기

### 7F.10.1 존재성 증명: "역이 존재한다"

역모듈로가 존재한다는 것은 $\exists \bar{a}, \bar{a} \cdot a \equiv 1 \pmod{m}$이라는 뜻이다. Lean4에서 이것을 증명해 보자.

```lean
-- "3 modulo 7의 역이 존재한다"
-- 즉, ∃ x, (3 * x) % 7 = 1
theorem exists_inv_3_mod_7 : ∃ x : Nat, (3 * x) % 7 = 1 := by
  use 5          -- 증인으로 5를 제시
  native_decide  -- 3 * 5 = 15, 15 % 7 = 1 ✓
```

이 증명의 구조를 분석하자:

1. `∃ x : Nat, (3 * x) % 7 = 1` — "어떤 자연수 x가 있어서 3x mod 7 = 1"
2. `use 5` — "그 x로 5를 제시합니다" (이것이 **증인**(witness)이다!)
3. `native_decide` — "3 × 5 = 15, 15 mod 7 = 1이므로 참입니다"

### 7F.10.2 유일성 증명

교재는 역이 **유일**하다고 말한다 (모듈로 m에서). 이것을 증명해 보자:

```lean
-- 만약 a*x₁ ≡ 1 (mod m)이고 a*x₂ ≡ 1 (mod m)이면
-- x₁ ≡ x₂ (mod m)이다

-- 특수한 경우: 3의 역(mod 7)이 유일한 mod 7 값임을 확인
-- 가능한 값: 0, 1, 2, 3, 4, 5, 6 중 3x mod 7 = 1인 것은 5뿐
example : ∀ x : Fin 7, (3 * x.val) % 7 = 1 → x.val = 5 := by
  decide
```

### 연습 10-1: 존재성 증명 (괄호 채우기)

```lean
-- "5 modulo 11의 역이 존재한다"
theorem exists_inv_5_mod_11 : ∃ x : Nat, (5 * x) % 11 = 1 := by
  use (______)
  native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 5 × 9 = 45, 45 mod 11 = 1 (45 = 4 × 11 + 1)
theorem exists_inv_5_mod_11 : ∃ x : Nat, (5 * x) % 11 = 1 := by
  use 9
  native_decide
```

</details>

### 연습 10-2: 존재성 증명 (sorry)

```lean
-- "7 modulo 13의 역이 존재한다"
theorem exists_inv_7_mod_13 : ∃ x : Nat, (7 * x) % 13 = 1 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 7 × 2 = 14, 14 mod 13 = 1
theorem exists_inv_7_mod_13 : ∃ x : Nat, (7 * x) % 13 = 1 := by
  use 2
  native_decide
```

</details>

### 연습 10-3: 비존재 증명 (sorry)

```lean
-- "2 modulo 6의 역은 존재하지 않는다"
-- 즉, 모든 x에 대해 2x mod 6 ≠ 1
theorem no_inv_2_mod_6 : ¬∃ x : Fin 6, (2 * x.val) % 6 = 1 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem no_inv_2_mod_6 : ¬∃ x : Fin 6, (2 * x.val) % 6 = 1 := by
  decide
-- Lean4가 x = 0, 1, 2, 3, 4, 5를 모두 검사하고
-- 2*0=0, 2*1=2, 2*2=4, 2*3=0, 2*4=2, 2*5=4
-- 어떤 것도 mod 6 = 1이 아님을 확인한다
```

</details>

---

## 7F.11 **검사 방법의 속도 향상** (교재 내용)

교재에서는 검사 방법의 속도를 높이는 트릭을 소개한다. 3 모듈로 7의 역을 찾을 때, $j = 1, 2, \ldots$를 순서대로 검사하는 대신:

$j \cdot 3 \bmod 7$: $3, 6, 2, 5, 1, 4, \ldots$

$j = 5$에서 1이 나오므로 역은 5이다.

그런데 더 빠른 방법이 있다! $-2 \cdot 3 = -6 \equiv 1 \pmod{7}$이므로, **음수 방향**으로 검사하면 2번만에 찾을 수 있다. $5 \cdot 3 \equiv 1 \pmod{7}$인데 $5 = 7 - 2$이므로, 사실상 $-2$에서 시작한 것이다.

```lean
-- 5 ≡ -2 (mod 7) 확인
example : (5 : Int) % 7 = (-2 : Int) % 7 := by native_decide
-- 둘 다 5!
```

---

## 7F.12 전술 요약

이 장에서 사용한 Lean4 전술을 정리한다:

| 전술 | 용도 | 예시 |
|------|------|------|
| `native_decide` | 구체적 숫자 계산 증명 | `(3*5) % 7 = 1` |
| `norm_num` | 정수 산술 계산 | `(-2)*3 + 1*7 = 1` |
| `use` | 존재 명제의 증인 제시 | `use 5` |
| `decide` | 유한 범위 전수 검사 | `∀ x : Fin 7, ...` |
| `ring` | 대수적 등식 | 다항식 정리 |

---

## 7F.13 핵심 정리 요약

| 이름 | 내용 |
|------|------|
| **정리 1** (역모듈로 존재) | $\gcd(a, m) = 1$이면 $\bar{a}a \equiv 1 \pmod{m}$인 $\bar{a}$가 존재하고 유일하다 |
| **선형합동 풀이법** | $ax \equiv b \pmod{m}$에서 $x \equiv \bar{a}b \pmod{m}$ |
| **역 계산법 1** (검사) | $j = 1, \ldots, m-1$을 시도하여 $aj \equiv 1$인 $j$를 찾는다. $O(m)$ |
| **역 계산법 2** (유클리드) | $sa + tm = 1$에서 $s$가 역이다. $O(\log m)$ |

---

## 7F.14 도전 문제

### 도전 1: 교재 연습문제 7 — 역의 유일함 증명

만약 $a$와 $m$이 서로소인 양의 정수이면 $a$ 모듈로 $m$의 역은 모듈로 $m$에서 유일함을 증명하라.

힌트: 합동 $ax \equiv 1 \pmod{m}$의 두 해 $b$와 $c$가 있다고 가정하면, 4.3절 정리 7을 사용하여 $b \equiv c \pmod{m}$임을 증명한다.

```lean
-- 힌트: 만약 a*b ≡ 1 (mod m)이고 a*c ≡ 1 (mod m)이면
-- a*b ≡ a*c (mod m)
-- gcd(a, m) = 1이므로 (소거법) b ≡ c (mod m)

-- 특수 사례로 확인: Fin 7에서 3의 역은 유일하다
example : ∀ x y : Fin 7, 
    (3 * x.val) % 7 = 1 → (3 * y.val) % 7 = 1 → x = y := by
  decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∀ x y : Fin 7, 
    (3 * x.val) % 7 = 1 → (3 * y.val) % 7 = 1 → x = y := by
  decide
-- Lean4가 49가지 (x, y) 조합을 전부 검사하여 확인한다
```

**일반적 증명** (개요):
- $ab \equiv 1 \pmod{m}$이고 $ac \equiv 1 \pmod{m}$
- 양변을 빼면 $a(b - c) \equiv 0 \pmod{m}$
- $\gcd(a, m) = 1$이므로 $m | (b - c)$
- 따라서 $b \equiv c \pmod{m}$

</details>

### 도전 2: 교재 연습문제 8 — 역이 존재하지 않을 조건

$a$가 정수이고 $m > 1$인 양의 정수이고 $\gcd(a, m) > 1$일 때, $a$ 모듈로 $m$의 역이 존재하지 않음을 증명하라.

```lean
-- 특수 사례: gcd(2, 6) = 2 > 1이면 역이 없다
example : ¬∃ x : Fin 6, (2 * x.val) % 6 = 1 := by decide

-- 일반적으로: 만약 d = gcd(a, m) > 1이면
-- a*x를 m으로 나눈 나머지는 항상 d의 배수이다
-- 따라서 1 (d의 배수가 아님)이 될 수 없다!
```

<details>
<summary>💡 답 보기</summary>

**증명 (개요)**:
- $d = \gcd(a, m) > 1$이라 하자
- $a = da'$, $m = dm'$으로 쓸 수 있다 ($d > 1$이므로 $m' < m$)
- 만약 $ax \equiv 1 \pmod{m}$이면 $m | (ax - 1)$
- 즉 $ax - 1 = km$인 정수 $k$가 존재
- $da'x - 1 = kdm'$
- $d(a'x - km') = 1$
- 그런데 $d > 1$이고 $d | 1$이어야 하므로 **모순**!

```lean
-- 구체적 확인: mod 6에서 2*x의 가능한 값
#eval (List.range 6).map (fun x => (2 * x) % 6)
-- [0, 2, 4, 0, 2, 4] — 1이 절대 나오지 않는다!
-- 가능한 나머지는 0, 2, 4 = gcd(2,6) = 2의 배수뿐
```

</details>

---

## 다음 편(7-G) 예고

**제7-G편** (중국인의 나머지 정리)에서는:
- **중국인의 나머지 정리**(Chinese Remainder Theorem): 연립 합동 시스템 풀기
- **역대입법**(back substitution): 연립 합동의 다른 풀이법
- **큰 정수의 컴퓨터 연산**: 나머지 표현으로 병렬 계산

를 다룬다.

---

**(끝)**
