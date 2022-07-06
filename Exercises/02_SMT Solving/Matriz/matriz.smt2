; --- 2. Faça a codificação lógica do programa que definiu na alı́nea anterior, num ficheiro em formato SMT-LIBv2. ---
(set-logic QF_AUFLIA)

; Variáveis necessárias a codificação lógica
(declare-fun M () (Array Int (Array Int Int)))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun a () Int)
(declare-fun b () Int)

; Conversão do programa criado previamente numa codificação lógica
(assert (= (select (select M 1) 1) 2))
(assert (= (select (select M 1) 2) 3))
(assert (= (select (select M 1) 3) 4))
(assert (= (select (select M 2) 1) 3))
(assert (= (select (select M 2) 2) 4))
(assert (= (select (select M 2) 3) 5))
(assert (= (select (select M 3) 1) 4))
(assert (= (select (select M 3) 2) 5))
(assert (= (select (select M 3) 3) 6))

; --- 3. Tendo por base a codificação lógica que fez do programa, use um SMT solver para estabelecer, no final ------
; ------ da execução do programa, a validade das propriedades que se seguem: ----------------------------------------
(echo "Verificação das seguintes propriedades (sat - Afirmação refutável; unsat - afirmação válida):")

; ------ (a) Se i = j então M[i][j] != 3. ---------------------------------------------------------------------------
(echo "")
(echo "a) Se i = j então M[i][j] != 3.")

(push)

;(assert (and (<= 1 i) (<= i 3)))
;(assert (and (<= 1 j) (<= j 3)))
(assert
    (not (=>
            (= i j)
            (not (= (select (select M i) j) 3))
    ))
)

(check-sat)

(pop)

; ------ (b) Para quaisquer i e j entre 1 e 3, M[i][j] = M[j][i]. ---------------------------------------------------
(echo "")
(echo "b) Para quaisquer i e j entre 1 e 3, M[i][j] = M[j][i].")

(push)

(assert (and (<= 1 i) (<= i 3)))
(assert (and (<= 1 j) (<= j 3)))
(assert
    (not (=
            (select (select M i) j)
            (select (select M j) i)
    ))
)

(check-sat)

(pop)

; ------ (c) Para quaisquer i e j entre 1 e 3, se i < j então M[i][j] < 6. ------------------------------------------
(echo "")
(echo "c) Para quaisquer i e j entre 1 e 3, se i < j então M[i][j] < 6.")

(push)

(assert (and (<= 1 i) (<= i 3)))
(assert (and (<= 1 j) (<= j 3)))
(assert
    (not (=>
            (< i j)
            (< (select (select M i) j) 6)
    ))
)

(check-sat)

(pop)

; ------ (d) Para quaisquer i, a e b entre 1 e 3, se a > b então M[i][a] > M[i][b]. ---------------------------------
(echo "")
(echo "d) Para quaisquer i, a e b entre 1 e 3, se a > b então M[i][a] > M[i][b].")

(push)

(assert (and (<= 1 i) (<= i 3)))
(assert (and (<= 1 a) (<= a 3)))
(assert (and (<= 1 b) (<= b 3)))
(assert
    (not (=>
            (> a b)
            (>
                (select (select M i) a)
                (select (select M i) b)
            )
    ))
)

(check-sat)

(pop)

; ------ (e) Para quaisquer i e j entre 1 e 3, M[i][j] + M[i+1][j+1] = M[i+1][j] + M[i][j+1]. -----------------------
(echo "")
(echo "e) Para quaisquer i e j entre 1 e 3, M[i][j] + M[i+1][j+1] = M[i+1][j] + M[i][j+1].")

(push)

(assert (and (<= 1 i) (<= i 3)))
(assert (and (<= 1 j) (<= j 3)))
;(assert (and (<= 1 i) (<= i 2)))
;(assert (and (<= 1 j) (<= j 2)))
(assert
    (not (=
            (+ 
                (select (select M i) j)
                (select (select M (+ i 1)) (+ j 1))
            )
            (+ 
                (select (select M (+ i 1)) j)
                (select (select M i) (+ j 1))
            )
    ))
)

(check-sat)

(pop)