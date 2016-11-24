abstract sig Charge {}
lone sig Euro1 extends Charge {}
lone sig NoCharge extends Charge{}

abstract sig Discount {}
lone sig Percent10 extends Discount {}
lone sig Percent20 extends Discount {}
lone sig Percent30 extends Discount {}
lone sig NoDiscount extends Discount {}

abstract sig Payment {
discounts: some Discount,
charges: some Charge 
} {
#discounts < 4
#charges < 3
}

fact {
all c: Car | d: c. 
(#discounts > 1) implies (discounts != 
}




sig Car {}

abstract sig Person {}
sig RegUser extends Person {


}







pred show() {}


run show
