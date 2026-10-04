; benchmark generated from python API
(set-info :status unknown)
(declare-fun n () Int)
(declare-fun t () Real)
(declare-fun d_01 () Real)
(declare-fun d_02 () Real)
(declare-fun d_03 () Real)
(declare-fun d_12 () Real)
(declare-fun d_13 () Real)
(declare-fun d_23 () Real)
(declare-fun f_00 () Int)
(declare-fun f_01 () Int)
(declare-fun f_02 () Int)
(declare-fun k_0 () Int)
(declare-fun f_10 () Int)
(declare-fun f_11 () Int)
(declare-fun f_12 () Int)
(declare-fun k_1 () Int)
(declare-fun f_20 () Int)
(declare-fun f_21 () Int)
(declare-fun f_22 () Int)
(declare-fun k_2 () Int)
(declare-fun f_30 () Int)
(declare-fun f_31 () Int)
(declare-fun f_32 () Int)
(declare-fun k_3 () Int)
(assert
 (>= n 2))
(assert
 (let ((?x9 (to_real n)))
 (>= t ?x9)))
(assert
 (< t (to_real (+ n 1))))
(assert
 (< t (+ (to_real n) (/ 1.0 2.0))))
(assert
 (>= d_01 0.0))
(assert
 (< d_01 t))
(assert
 (>= d_02 0.0))
(assert
 (< d_02 t))
(assert
 (>= d_03 0.0))
(assert
 (< d_03 t))
(assert
 (>= d_12 0.0))
(assert
 (< d_12 t))
(assert
 (>= d_13 0.0))
(assert
 (< d_13 t))
(assert
 (>= d_23 0.0))
(assert
 (< d_23 t))
(assert
 (let (($x125 (and (< d_12 d_02) (< d_02 d_01) (>= (- d_01 d_12) 1.0) (<= (- d_01 d_02) (- t 1.0)) (<= (- d_02 d_12) (- t 1.0)))))
 (let (($x108 (< d_02 d_12)))
 (let (($x107 (< d_01 d_02)))
 (let (($x116 (and $x107 $x108 (>= (- d_12 d_01) 1.0) (<= (- d_02 d_01) (- t 1.0)) (<= (- d_12 d_02) (- t 1.0)))))
 (or $x116 $x125))))))
(assert
 (let (($x185 (and (< d_13 d_03) (< d_03 d_01) (>= (- d_01 d_13) 1.0) (<= (- d_01 d_03) (- t 1.0)) (<= (- d_03 d_13) (- t 1.0)))))
 (let (($x169 (< d_03 d_13)))
 (let (($x168 (< d_01 d_03)))
 (let (($x176 (and $x168 $x169 (>= (- d_13 d_01) 1.0) (<= (- d_03 d_01) (- t 1.0)) (<= (- d_13 d_03) (- t 1.0)))))
 (or $x176 $x185))))))
(assert
 (let (($x242 (and (< d_23 d_03) (< d_03 d_02) (>= (- d_02 d_23) 1.0) (<= (- d_02 d_03) (- t 1.0)) (<= (- d_03 d_23) (- t 1.0)))))
 (let (($x226 (< d_03 d_23)))
 (let (($x225 (< d_02 d_03)))
 (let (($x233 (and $x225 $x226 (>= (- d_23 d_02) 1.0) (<= (- d_03 d_02) (- t 1.0)) (<= (- d_23 d_03) (- t 1.0)))))
 (or $x233 $x242))))))
(assert
 (let (($x299 (and (< d_23 d_13) (< d_13 d_12) (>= (- d_12 d_23) 1.0) (<= (- d_12 d_13) (- t 1.0)) (<= (- d_13 d_23) (- t 1.0)))))
 (let (($x283 (< d_13 d_23)))
 (let (($x282 (< d_12 d_13)))
 (let (($x290 (and $x282 $x283 (>= (- d_23 d_12) 1.0) (<= (- d_13 d_12) (- t 1.0)) (<= (- d_23 d_13) (- t 1.0)))))
 (or $x290 $x299))))))
(assert
 (>= f_00 0))
(assert
 (let (($x107 (< d_01 d_02)))
 (let ((?x341 (ite $x107 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x347 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let ((?x351 (- (- (+ (+ d_01 d_02) d_03) ?x341) ?x347)))
 (let ((?x352 (- ?x351 ?x341)))
 (let ((?x361 (to_real f_00)))
 (<= ?x361 ?x352))))))))
(assert
 (let (($x107 (< d_01 d_02)))
 (let ((?x341 (ite $x107 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x347 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let ((?x351 (- (- (+ (+ d_01 d_02) d_03) ?x341) ?x347)))
 (let ((?x352 (- ?x351 ?x341)))
 (< ?x352 (to_real (+ f_00 1)))))))))
(assert
 (>= f_01 0))
(assert
 (let ((?x347 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let (($x107 (< d_01 d_02)))
 (let ((?x341 (ite $x107 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x351 (- (- (+ (+ d_01 d_02) d_03) ?x341) ?x347)))
 (let ((?x353 (- ?x347 ?x351)))
 (let ((?x394 (to_real f_01)))
 (<= ?x394 ?x353))))))))
(assert
 (let ((?x347 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let (($x107 (< d_01 d_02)))
 (let ((?x341 (ite $x107 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x351 (- (- (+ (+ d_01 d_02) d_03) ?x341) ?x347)))
 (let ((?x353 (- ?x347 ?x351)))
 (< ?x353 (to_real (+ f_01 1)))))))))
(assert
 (>= f_02 0))
(assert
 (let ((?x347 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let (($x107 (< d_01 d_02)))
 (let ((?x341 (ite $x107 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x355 (- (+ t ?x341) ?x347)))
 (let ((?x417 (to_real f_02)))
 (<= ?x417 ?x355)))))))
(assert
 (let ((?x347 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let (($x107 (< d_01 d_02)))
 (let ((?x341 (ite $x107 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x355 (- (+ t ?x341) ?x347)))
 (< ?x355 (to_real (+ f_02 1))))))))
(assert
 (let ((?x444 (+ (ite (>= f_00 2) (- f_00 1) 0) (ite (>= f_01 2) (- f_01 1) 0) (ite (>= f_02 2) (- f_02 1) 0))))
 (= k_0 ?x444)))
(assert
 (>= k_0 0))
(assert
 (let ((?x463 (- n 1)))
 (<= k_0 ?x463)))
(assert
 (>= f_10 0))
(assert
 (let ((?x474 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x480 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x484 (- (- (+ (+ d_01 d_12) d_13) ?x474) ?x480)))
 (let ((?x485 (- ?x484 ?x474)))
 (let ((?x493 (to_real f_10)))
 (<= ?x493 ?x485)))))))
(assert
 (let ((?x474 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x480 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x484 (- (- (+ (+ d_01 d_12) d_13) ?x474) ?x480)))
 (let ((?x485 (- ?x484 ?x474)))
 (< ?x485 (to_real (+ f_10 1))))))))
(assert
 (>= f_11 0))
(assert
 (let ((?x480 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x474 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x484 (- (- (+ (+ d_01 d_12) d_13) ?x474) ?x480)))
 (let ((?x486 (- ?x480 ?x484)))
 (let ((?x540 (to_real f_11)))
 (<= ?x540 ?x486)))))))
(assert
 (let ((?x480 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x474 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x484 (- (- (+ (+ d_01 d_12) d_13) ?x474) ?x480)))
 (let ((?x486 (- ?x480 ?x484)))
 (< ?x486 (to_real (+ f_11 1))))))))
(assert
 (>= f_12 0))
(assert
 (let ((?x480 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x474 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x488 (- (+ t ?x474) ?x480)))
 (let ((?x563 (to_real f_12)))
 (<= ?x563 ?x488))))))
(assert
 (let ((?x480 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x474 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x488 (- (+ t ?x474) ?x480)))
 (< ?x488 (to_real (+ f_12 1)))))))
(assert
 (let ((?x590 (+ (ite (>= f_10 2) (- f_10 1) 0) (ite (>= f_11 2) (- f_11 1) 0) (ite (>= f_12 2) (- f_12 1) 0))))
 (= k_1 ?x590)))
(assert
 (>= k_1 0))
(assert
 (let ((?x463 (- n 1)))
 (<= k_1 ?x463)))
(assert
 (>= f_20 0))
(assert
 (let (($x108 (< d_02 d_12)))
 (let ((?x615 (ite $x108 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x621 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let ((?x625 (- (- (+ (+ d_02 d_12) d_23) ?x615) ?x621)))
 (let ((?x626 (- ?x625 ?x615)))
 (let ((?x634 (to_real f_20)))
 (<= ?x634 ?x626))))))))
(assert
 (let (($x108 (< d_02 d_12)))
 (let ((?x615 (ite $x108 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x621 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let ((?x625 (- (- (+ (+ d_02 d_12) d_23) ?x615) ?x621)))
 (let ((?x626 (- ?x625 ?x615)))
 (< ?x626 (to_real (+ f_20 1)))))))))
(assert
 (>= f_21 0))
(assert
 (let ((?x621 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let (($x108 (< d_02 d_12)))
 (let ((?x615 (ite $x108 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x625 (- (- (+ (+ d_02 d_12) d_23) ?x615) ?x621)))
 (let ((?x627 (- ?x621 ?x625)))
 (let ((?x681 (to_real f_21)))
 (<= ?x681 ?x627))))))))
(assert
 (let ((?x621 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let (($x108 (< d_02 d_12)))
 (let ((?x615 (ite $x108 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x625 (- (- (+ (+ d_02 d_12) d_23) ?x615) ?x621)))
 (let ((?x627 (- ?x621 ?x625)))
 (< ?x627 (to_real (+ f_21 1)))))))))
(assert
 (>= f_22 0))
(assert
 (let ((?x621 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let (($x108 (< d_02 d_12)))
 (let ((?x615 (ite $x108 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x629 (- (+ t ?x615) ?x621)))
 (let ((?x704 (to_real f_22)))
 (<= ?x704 ?x629)))))))
(assert
 (let ((?x621 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let (($x108 (< d_02 d_12)))
 (let ((?x615 (ite $x108 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x629 (- (+ t ?x615) ?x621)))
 (< ?x629 (to_real (+ f_22 1))))))))
(assert
 (let ((?x731 (+ (ite (>= f_20 2) (- f_20 1) 0) (ite (>= f_21 2) (- f_21 1) 0) (ite (>= f_22 2) (- f_22 1) 0))))
 (= k_2 ?x731)))
(assert
 (>= k_2 0))
(assert
 (let ((?x463 (- n 1)))
 (<= k_2 ?x463)))
(assert
 (>= f_30 0))
(assert
 (let (($x169 (< d_03 d_13)))
 (let ((?x754 (ite $x169 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x760 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let ((?x764 (- (- (+ (+ d_03 d_13) d_23) ?x754) ?x760)))
 (let ((?x765 (- ?x764 ?x754)))
 (let ((?x773 (to_real f_30)))
 (<= ?x773 ?x765))))))))
(assert
 (let (($x169 (< d_03 d_13)))
 (let ((?x754 (ite $x169 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x760 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let ((?x764 (- (- (+ (+ d_03 d_13) d_23) ?x754) ?x760)))
 (let ((?x765 (- ?x764 ?x754)))
 (< ?x765 (to_real (+ f_30 1)))))))))
(assert
 (>= f_31 0))
(assert
 (let ((?x760 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let (($x169 (< d_03 d_13)))
 (let ((?x754 (ite $x169 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x764 (- (- (+ (+ d_03 d_13) d_23) ?x754) ?x760)))
 (let ((?x766 (- ?x760 ?x764)))
 (let ((?x804 (to_real f_31)))
 (<= ?x804 ?x766))))))))
(assert
 (let ((?x760 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let (($x169 (< d_03 d_13)))
 (let ((?x754 (ite $x169 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x764 (- (- (+ (+ d_03 d_13) d_23) ?x754) ?x760)))
 (let ((?x766 (- ?x760 ?x764)))
 (< ?x766 (to_real (+ f_31 1)))))))))
(assert
 (>= f_32 0))
(assert
 (let ((?x760 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let (($x169 (< d_03 d_13)))
 (let ((?x754 (ite $x169 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x768 (- (+ t ?x754) ?x760)))
 (let ((?x827 (to_real f_32)))
 (<= ?x827 ?x768)))))))
(assert
 (let ((?x760 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let (($x169 (< d_03 d_13)))
 (let ((?x754 (ite $x169 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x768 (- (+ t ?x754) ?x760)))
 (< ?x768 (to_real (+ f_32 1))))))))
(assert
 (let ((?x854 (+ (ite (>= f_30 2) (- f_30 1) 0) (ite (>= f_31 2) (- f_31 1) 0) (ite (>= f_32 2) (- f_32 1) 0))))
 (= k_3 ?x854)))
(assert
 (>= k_3 0))
(assert
 (let ((?x463 (- n 1)))
 (<= k_3 ?x463)))
(assert
 (let ((?x893 (+ (ite (>= k_0 (- n 2)) 1 0) (ite (>= k_1 (- n 2)) 1 0) (ite (>= k_2 (- n 2)) 1 0) (ite (>= k_3 (- n 2)) 1 0))))
(let ((?x883 (+ (ite (= k_0 (- n 1)) 1 0) (ite (= k_1 (- n 1)) 1 0) (ite (= k_2 (- n 1)) 1 0) (ite (= k_3 (- n 1)) 1 0))))
(or (>= ?x883 2) (and (>= ?x883 1) (>= ?x893 3))))))
(check-sat)
