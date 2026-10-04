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
 (>= t (+ (to_real n) (/ 1.0 2.0))))
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
 (let (($x121 (and (< d_12 d_02) (< d_02 d_01) (>= (- d_01 d_12) 1.0) (<= (- d_01 d_02) (- t 1.0)) (<= (- d_02 d_12) (- t 1.0)))))
 (let (($x104 (< d_02 d_12)))
 (let (($x103 (< d_01 d_02)))
 (let (($x112 (and $x103 $x104 (>= (- d_12 d_01) 1.0) (<= (- d_02 d_01) (- t 1.0)) (<= (- d_12 d_02) (- t 1.0)))))
 (or $x112 $x121))))))
(assert
 (let (($x181 (and (< d_13 d_03) (< d_03 d_01) (>= (- d_01 d_13) 1.0) (<= (- d_01 d_03) (- t 1.0)) (<= (- d_03 d_13) (- t 1.0)))))
 (let (($x165 (< d_03 d_13)))
 (let (($x164 (< d_01 d_03)))
 (let (($x172 (and $x164 $x165 (>= (- d_13 d_01) 1.0) (<= (- d_03 d_01) (- t 1.0)) (<= (- d_13 d_03) (- t 1.0)))))
 (or $x172 $x181))))))
(assert
 (let (($x238 (and (< d_23 d_03) (< d_03 d_02) (>= (- d_02 d_23) 1.0) (<= (- d_02 d_03) (- t 1.0)) (<= (- d_03 d_23) (- t 1.0)))))
 (let (($x222 (< d_03 d_23)))
 (let (($x221 (< d_02 d_03)))
 (let (($x229 (and $x221 $x222 (>= (- d_23 d_02) 1.0) (<= (- d_03 d_02) (- t 1.0)) (<= (- d_23 d_03) (- t 1.0)))))
 (or $x229 $x238))))))
(assert
 (let (($x295 (and (< d_23 d_13) (< d_13 d_12) (>= (- d_12 d_23) 1.0) (<= (- d_12 d_13) (- t 1.0)) (<= (- d_13 d_23) (- t 1.0)))))
 (let (($x279 (< d_13 d_23)))
 (let (($x278 (< d_12 d_13)))
 (let (($x286 (and $x278 $x279 (>= (- d_23 d_12) 1.0) (<= (- d_13 d_12) (- t 1.0)) (<= (- d_23 d_13) (- t 1.0)))))
 (or $x286 $x295))))))
(assert
 (>= f_00 0))
(assert
 (let (($x103 (< d_01 d_02)))
 (let ((?x337 (ite $x103 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x343 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let ((?x347 (- (- (+ (+ d_01 d_02) d_03) ?x337) ?x343)))
 (let ((?x348 (- ?x347 ?x337)))
 (let ((?x357 (to_real f_00)))
 (<= ?x357 ?x348))))))))
(assert
 (let (($x103 (< d_01 d_02)))
 (let ((?x337 (ite $x103 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x343 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let ((?x347 (- (- (+ (+ d_01 d_02) d_03) ?x337) ?x343)))
 (let ((?x348 (- ?x347 ?x337)))
 (< ?x348 (to_real (+ f_00 1)))))))))
(assert
 (>= f_01 0))
(assert
 (let ((?x343 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let (($x103 (< d_01 d_02)))
 (let ((?x337 (ite $x103 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x347 (- (- (+ (+ d_01 d_02) d_03) ?x337) ?x343)))
 (let ((?x349 (- ?x343 ?x347)))
 (let ((?x390 (to_real f_01)))
 (<= ?x390 ?x349))))))))
(assert
 (let ((?x343 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let (($x103 (< d_01 d_02)))
 (let ((?x337 (ite $x103 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x347 (- (- (+ (+ d_01 d_02) d_03) ?x337) ?x343)))
 (let ((?x349 (- ?x343 ?x347)))
 (< ?x349 (to_real (+ f_01 1)))))))))
(assert
 (>= f_02 0))
(assert
 (let ((?x343 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let (($x103 (< d_01 d_02)))
 (let ((?x337 (ite $x103 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x351 (- (+ t ?x337) ?x343)))
 (let ((?x413 (to_real f_02)))
 (<= ?x413 ?x351)))))))
(assert
 (let ((?x343 (ite (> d_01 d_02) (ite (> d_01 d_03) d_01 d_03) (ite (> d_02 d_03) d_02 d_03))))
 (let (($x103 (< d_01 d_02)))
 (let ((?x337 (ite $x103 (ite (< d_01 d_03) d_01 d_03) (ite (< d_02 d_03) d_02 d_03))))
 (let ((?x351 (- (+ t ?x337) ?x343)))
 (< ?x351 (to_real (+ f_02 1))))))))
(assert
 (let ((?x440 (+ (ite (>= f_00 2) (- f_00 1) 0) (ite (>= f_01 2) (- f_01 1) 0) (ite (>= f_02 2) (- f_02 1) 0))))
 (= k_0 ?x440)))
(assert
 (>= k_0 0))
(assert
 (let ((?x459 (- n 1)))
 (<= k_0 ?x459)))
(assert
 (>= f_10 0))
(assert
 (let ((?x470 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x476 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x480 (- (- (+ (+ d_01 d_12) d_13) ?x470) ?x476)))
 (let ((?x481 (- ?x480 ?x470)))
 (let ((?x489 (to_real f_10)))
 (<= ?x489 ?x481)))))))
(assert
 (let ((?x470 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x476 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x480 (- (- (+ (+ d_01 d_12) d_13) ?x470) ?x476)))
 (let ((?x481 (- ?x480 ?x470)))
 (< ?x481 (to_real (+ f_10 1))))))))
(assert
 (>= f_11 0))
(assert
 (let ((?x476 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x470 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x480 (- (- (+ (+ d_01 d_12) d_13) ?x470) ?x476)))
 (let ((?x482 (- ?x476 ?x480)))
 (let ((?x536 (to_real f_11)))
 (<= ?x536 ?x482)))))))
(assert
 (let ((?x476 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x470 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x480 (- (- (+ (+ d_01 d_12) d_13) ?x470) ?x476)))
 (let ((?x482 (- ?x476 ?x480)))
 (< ?x482 (to_real (+ f_11 1))))))))
(assert
 (>= f_12 0))
(assert
 (let ((?x476 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x470 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x484 (- (+ t ?x470) ?x476)))
 (let ((?x559 (to_real f_12)))
 (<= ?x559 ?x484))))))
(assert
 (let ((?x476 (ite (> d_01 d_12) (ite (> d_01 d_13) d_01 d_13) (ite (> d_12 d_13) d_12 d_13))))
 (let ((?x470 (ite (< d_01 d_12) (ite (< d_01 d_13) d_01 d_13) (ite (< d_12 d_13) d_12 d_13))))
 (let ((?x484 (- (+ t ?x470) ?x476)))
 (< ?x484 (to_real (+ f_12 1)))))))
(assert
 (let ((?x586 (+ (ite (>= f_10 2) (- f_10 1) 0) (ite (>= f_11 2) (- f_11 1) 0) (ite (>= f_12 2) (- f_12 1) 0))))
 (= k_1 ?x586)))
(assert
 (>= k_1 0))
(assert
 (let ((?x459 (- n 1)))
 (<= k_1 ?x459)))
(assert
 (>= f_20 0))
(assert
 (let (($x104 (< d_02 d_12)))
 (let ((?x611 (ite $x104 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x617 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let ((?x621 (- (- (+ (+ d_02 d_12) d_23) ?x611) ?x617)))
 (let ((?x622 (- ?x621 ?x611)))
 (let ((?x630 (to_real f_20)))
 (<= ?x630 ?x622))))))))
(assert
 (let (($x104 (< d_02 d_12)))
 (let ((?x611 (ite $x104 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x617 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let ((?x621 (- (- (+ (+ d_02 d_12) d_23) ?x611) ?x617)))
 (let ((?x622 (- ?x621 ?x611)))
 (< ?x622 (to_real (+ f_20 1)))))))))
(assert
 (>= f_21 0))
(assert
 (let ((?x617 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let (($x104 (< d_02 d_12)))
 (let ((?x611 (ite $x104 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x621 (- (- (+ (+ d_02 d_12) d_23) ?x611) ?x617)))
 (let ((?x623 (- ?x617 ?x621)))
 (let ((?x677 (to_real f_21)))
 (<= ?x677 ?x623))))))))
(assert
 (let ((?x617 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let (($x104 (< d_02 d_12)))
 (let ((?x611 (ite $x104 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x621 (- (- (+ (+ d_02 d_12) d_23) ?x611) ?x617)))
 (let ((?x623 (- ?x617 ?x621)))
 (< ?x623 (to_real (+ f_21 1)))))))))
(assert
 (>= f_22 0))
(assert
 (let ((?x617 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let (($x104 (< d_02 d_12)))
 (let ((?x611 (ite $x104 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x625 (- (+ t ?x611) ?x617)))
 (let ((?x700 (to_real f_22)))
 (<= ?x700 ?x625)))))))
(assert
 (let ((?x617 (ite (> d_02 d_12) (ite (> d_02 d_23) d_02 d_23) (ite (> d_12 d_23) d_12 d_23))))
 (let (($x104 (< d_02 d_12)))
 (let ((?x611 (ite $x104 (ite (< d_02 d_23) d_02 d_23) (ite (< d_12 d_23) d_12 d_23))))
 (let ((?x625 (- (+ t ?x611) ?x617)))
 (< ?x625 (to_real (+ f_22 1))))))))
(assert
 (let ((?x727 (+ (ite (>= f_20 2) (- f_20 1) 0) (ite (>= f_21 2) (- f_21 1) 0) (ite (>= f_22 2) (- f_22 1) 0))))
 (= k_2 ?x727)))
(assert
 (>= k_2 0))
(assert
 (let ((?x459 (- n 1)))
 (<= k_2 ?x459)))
(assert
 (>= f_30 0))
(assert
 (let (($x165 (< d_03 d_13)))
 (let ((?x750 (ite $x165 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x756 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let ((?x760 (- (- (+ (+ d_03 d_13) d_23) ?x750) ?x756)))
 (let ((?x761 (- ?x760 ?x750)))
 (let ((?x769 (to_real f_30)))
 (<= ?x769 ?x761))))))))
(assert
 (let (($x165 (< d_03 d_13)))
 (let ((?x750 (ite $x165 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x756 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let ((?x760 (- (- (+ (+ d_03 d_13) d_23) ?x750) ?x756)))
 (let ((?x761 (- ?x760 ?x750)))
 (< ?x761 (to_real (+ f_30 1)))))))))
(assert
 (>= f_31 0))
(assert
 (let ((?x756 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let (($x165 (< d_03 d_13)))
 (let ((?x750 (ite $x165 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x760 (- (- (+ (+ d_03 d_13) d_23) ?x750) ?x756)))
 (let ((?x762 (- ?x756 ?x760)))
 (let ((?x800 (to_real f_31)))
 (<= ?x800 ?x762))))))))
(assert
 (let ((?x756 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let (($x165 (< d_03 d_13)))
 (let ((?x750 (ite $x165 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x760 (- (- (+ (+ d_03 d_13) d_23) ?x750) ?x756)))
 (let ((?x762 (- ?x756 ?x760)))
 (< ?x762 (to_real (+ f_31 1)))))))))
(assert
 (>= f_32 0))
(assert
 (let ((?x756 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let (($x165 (< d_03 d_13)))
 (let ((?x750 (ite $x165 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x764 (- (+ t ?x750) ?x756)))
 (let ((?x823 (to_real f_32)))
 (<= ?x823 ?x764)))))))
(assert
 (let ((?x756 (ite (> d_03 d_13) (ite (> d_03 d_23) d_03 d_23) (ite (> d_13 d_23) d_13 d_23))))
 (let (($x165 (< d_03 d_13)))
 (let ((?x750 (ite $x165 (ite (< d_03 d_23) d_03 d_23) (ite (< d_13 d_23) d_13 d_23))))
 (let ((?x764 (- (+ t ?x750) ?x756)))
 (< ?x764 (to_real (+ f_32 1))))))))
(assert
 (let ((?x850 (+ (ite (>= f_30 2) (- f_30 1) 0) (ite (>= f_31 2) (- f_31 1) 0) (ite (>= f_32 2) (- f_32 1) 0))))
 (= k_3 ?x850)))
(assert
 (>= k_3 0))
(assert
 (let ((?x459 (- n 1)))
 (<= k_3 ?x459)))
(assert
 (let ((?x879 (+ (ite (= k_0 (- n 1)) 1 0) (ite (= k_1 (- n 1)) 1 0) (ite (= k_2 (- n 1)) 1 0) (ite (= k_3 (- n 1)) 1 0))))
 (>= ?x879 2)))
(assert
 (let ((?x889 (+ (ite (>= k_0 (- n 2)) 1 0) (ite (>= k_1 (- n 2)) 1 0) (ite (>= k_2 (- n 2)) 1 0) (ite (>= k_3 (- n 2)) 1 0))))
(>= ?x889 3)))
(check-sat)
