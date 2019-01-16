; Şükrü Can Gültop
; 2014400201
; Cmpe 480 A.I Project 2

;---------------------------------TEMPLATES-----------------------------------------

;answers template, it has id and answer list which contains yes and no as elements.

;e.g (answers (id 5) (answer (yes, no, yes, yes))

(deftemplate answers (slot id)  (multislot answer))

 

;illness template, it has three slots, name as illness name, prob as prior a,

;and sympthoms format is like that ((answer# P(answer=yes | prob) P(answer=yes | ~prob))+)

;e.g (illness (name "COMMON COLD") (prob 0.50) (symptoms (50 0.23 0.45 22 0.1 1 34 0.45 0)))

(deftemplate illness (slot name) (slot prob) (multislot symptoms))


;output template, it has three slots, name expects illness name, id which is same as input(patient), calculated number which represents a of illness,

;e.g(of answer exapmle) (output (name "COMMON COLD") (id 5) (0.85))

(deftemplate output (slot name) (slot id) (slot prob))

 

;---------------------------------FUNCTIONS-----------------------------------------
 
;String replace function

;Replaces all the occurences which are given as third parameter(?repl), with given string in the second parameter(?with)

;in input string which is first parameter (?str)

(deffunction str-replace (?str ?with ?repl)

    (if (eq ?repl "") then (return ?str))

    (bind ?rv "")

    (bind ?i (str-index ?repl ?str))

    (while ?i

        (bind ?rv (str-cat ?rv (sub-string 1 (- ?i 1) ?str) ?with))

        (bind ?str (sub-string (+ ?i (str-length ?repl )) (str-length ?str) ?str))

        (bind ?i (str-index ?repl ?str))
        
    )

    (bind ?rv (str-cat ?rv ?str))
)



;Reads the input file given in the parameter ?inputs.

;Firstly it replaces all the "," with whitespaces of read line to parse with explode$ function.

;After parsing the line it asserts corresponding answer and output of that answer facts.

(deffunction input-read (?inputs)

    (bind ?line (str-replace (readline ?inputs) " " ","))

    (while TRUE do

        (bind ?ans (explode$ ?line))

        (if (eq (nth$ 1 ?ans) EOF) then (break))

        (assert (answers (id (nth$ 1 ?ans)) (answer (rest$ ?ans))))

        (assert (output (name "") (id (nth$ 1 ?ans)) (prob 0)))

        (bind ?line (str-replace (readline ?inputs) " " ","))

    )
)

   

;Reads the Illness file given in the parameter ?inputs

;Firstly, it reads a line from file and gets the name of illness and after that it gets all the remaining list until 999 is reached

;The first item of this remaining list is prob of illness and remaining of this list is sympthoms.

;After binding name and list it asserts with information given above to assert illness.

(deffunction illness-read (?inputs)
    (while TRUE do

        (bind ?line (readline ?inputs))

        (if (eq ?line EOF) then (break))

        (bind ?indx (str-index  "," ?line))

        (bind ?name (sub-string 0 (- ?indx 1) ?line))

        (bind ?list (explode$ (str-replace (sub-string ?indx (- (str-index "999" ?line) 1) ?line) " " ",")))

        (assert (illness (name ?name) (prob (nth$ 1 ?list)) (symptoms (rest$ ?list ) )))

    )

)

; In this function probabilities of a patient whose answers to sympthoms are stored in ?answers variable, are calculated according to naive bayes classifier formula
     
; The ?prob variable is a ilness's prior probability and ?probs contains sympthom number and P(Answer=Yes |I) P(Answer = Yes | ~I) where I is a of having that illness.

;e.g (answers (yes no yes yes no))
;    (?prob 0.02)
;    (?probs (5 0.01 0.02 63 0.23 1))

; Function first gets prior probability and starts to read symphom number according to answer it calculates P(Answer=Yes | I) and P(Answer = No | I) with ?probs.
; after that it calculates denominator which can be either P(Answer = Yes) or P(Answer = No) with the help of ?probs information.

(deffunction calc-probs (?answers ?prob ?probs)

    (bind ?ret ?prob)

    (bind ?cnt 1)

    (while (<= ?cnt (length$ ?probs))

        (bind ?sympNo (nth$ ?cnt ?probs))

        (if (eq (nth$ ?sympNo ?answers) yes)

            then

            (bind ?ret (* ?ret (nth$ (+ 1 ?cnt) ?probs)))

            (bind ?denominator (+ (* ?prob (nth$ (+ 1 ?cnt) ?probs)) (* (- 1 ?prob) (nth$ (+ 2 ?cnt) ?probs))))

            (bind ?ret (/ ?ret ?denominator))

        )

        (if (eq (nth$ ?sympNo ?answers) no)

            then

            (bind ?ret (* ?ret (- 1 (nth$ (+ 1 ?cnt) ?probs))))

            (bind ?denominator (+ (* ?prob (- 1 (nth$ (+ 1 ?cnt) ?probs))) (* (- 1 ?prob) (- 1 (nth$ (+ 2 ?cnt) ?probs)))))

            (bind ?ret (/ ?ret ?denominator))

        )

        (bind ?cnt (+ ?cnt 3))

    )

    (return ?ret)

)

;---------------------------------RULES-----------------------------------------


;Starts the execution and calls reading functions of IlLNESS.TXT and INPUTS.TXT

(defrule startup
  =>
    (close)
    (open "INPUTS.txt" inputs)
    (open "ILLNESS.TXT" illness)
    (open "OUTPUTS.txt" outputs "w")
    (input-read inputs)
    (illness-read illness)
    (close inputs)
    (close illness)
)

;for every answers and illness pair it calls calcprob function to calculate a of this illness in given answers input,

;if this a is bigger then current a it changes the output illness to this illness with this calculated a.

(defrule a

    ?ans <- (answers (id ?id) (answer $?answers))

    ?output <- (output (id ?id) (name ?) (prob ?outProb))

    (illness (name ?name) (prob ?prob) (symptoms $?probs))

    =>

    (bind ?calcprob (calc-probs ?answers ?prob ?probs))

    (if (> ?calcprob ?outProb)

        then

       (modify ?output (name ?name) (prob ?calcprob))

    )

)

; Writes output facts to output file.
;
(defrule writeOutput
    ?out <- (output (id ?id) (name ?name))

    =>

    (printout outputs ?id "," ?name crlf)

    (retract ?out)
)

; if all the output facts are written to file it closes the file.

(defrule closeOutputs

    (not (output (id ?id)))

    =>

    (close outputs)
)
