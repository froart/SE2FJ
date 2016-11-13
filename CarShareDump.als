// ALLOY SPECIFICATION 
// FOR CARSHARING SYSTEM RASD
// AUTHOR: ARTEMIY FROLOV

// PEOPLE
// ============================================================================

// Any person
abstract sig Person{}
// Registered User
sig RegUser extends Person {
payment: lone Payment
} 

// OK
fact NoUserCanUseTheSameCar {
no disjoint c1, c2: Car | (c1.takenby = c2.takenby)
}


// OK
fact NoTheSamePassengers {
no disjoint c1, c2: Car | (c1.passengers & c2.passengers) != none
no disjoint c1,c2: Car | (c1.takenby in c2.passengers)
}



// Unregistered User
sig UnReg extends Person {}{ 
// unregistered users cannot use a car (can be done in Reqs)
}



// PAYMENT
// ============================================================================
// Discounts
abstract sig Discount {}
// Possible discounts
lone sig Discount10Percent extends Discount {}
lone sig Discount20Percent extends Discount {}
lone sig Discount30Percent extends Discount {}
// Charges
abstract sig Charge {}
// Possible Charges
lone sig Euro1 extends Charge{}
//
sig Receipt {} {
#Receipt >= 0
no disjoint c1, c2: Car | (c1.takenby.payment.total = c2.takenby.payment.total)
}


sig Payment {
total: lone Receipt,
discounts: Discount,
charges: Charge
} 
{
no total implies (#charges = 0) && (#discounts = 0) 
else
(#discounts >= 0) && (#charges >= 0)
}


// PARKING
// ============================================================================
abstract sig Parked {}
sig SpecialParkingArea extends Parked{}
sig AnyParkingArea extends Parked {}
lone sig Driven extends Parked{}


// TIME
// ============================================================================
abstract sig Time {}
lone sig Less1h extends Time{}
lone sig More1h extends Time{}

// CAR
// ============================================================================

// Car occupation states
abstract sig CarOccupationState {}
lone sig Available extends CarOccupationState {}
lone sig Reserved extends CarOccupationState {}
lone sig Occupied extends CarOccupationState {}
lone sig Released extends CarOccupationState {}
lone sig LostReservation extends CarOccupationState {}
lone sig LostOccupation extends CarOccupationState {}

// Car charging states
abstract sig CarChargingState {}
lone sig Charging extends CarChargingState {}
lone sig NotCharging extends CarChargingState {}

// Battery fulness
abstract sig BatteryFulness {}
lone sig More50 extends BatteryFulness {}
lone sig Less20 extends BatteryFulness {}
lone sig More20Less50 extends BatteryFulness {}

// Engine State
abstract sig CarEngineState {}
lone sig EngineOn extends CarEngineState {}
lone sig EngineOff extends CarEngineState {}

// Car
sig Car {
occupationstate: one CarOccupationState, // wether car is available, reserved, occupied or released
chargingstate: one CarChargingState, // wether car is charging or not 
takenby: lone RegUser, // car can either have a RegUser or not
passengers: Person, // can carry some persons
battery: one BatteryFulness, // battery fulness
parked: one Parked,
enginestate: one CarEngineState,
reservationtime: lone Time
} {
#passengers >= 0
#passengers <= 4
}




// CONVENTIONS
// ============================================================================

// occupationstate: one CarOccupationState, // wether car is available, reserved, occupied or released
/* Available state implies:
1. no RegUser in Car.takenby, no passengers
2. must be parked
3. can be charged
4. no reservationtime
5. no payment
6. Engine is off ahahah
*/
fact CarIsAvailableConventions {
all c: Car | (c.occupationstate = Available) implies {
// 1.
c.takenby = none
c.passengers = none
// 2. 
c.parked != Driven
// 3. 
// no need to implement
// 4.
c.reservationtime = none
//5.
no c.takenby.payment.total
}}



/* Reserved state implies:
1.1. RegUser in Car.takenby, 
1.2. no passengers. It means that Car.takenby has RegUser, but neither RegUser is in Car.passengers nor any other Person
2. must be parked
3. can be charged
4.1. reservation time must be set. 
5. User don't have payment
6. engine off
*/
fact CarIsReservedConventions {
all c: Car | (c.occupationstate = Reserved) implies {
// 1.1.
c.takenby != none
//1.2.
c.passengers = none
// 2.
c.parked != Driven
// 3. 
// no need to implement
// 4.1.
c.reservationtime = Less1h
//5.
no c.takenby.payment.total
//6.
//c.enginestate = EngineOff
}}


/*LostReservation state implies
1.1. No RegUser in Car.takenby
1.2. No passengers
2. Engine must be off
3. reservationtime must be More1h
4. User must have payment 1 euro
*/
fact CarIsLostReservation {
all c: Car | (c.occupationstate = LostReservation) implies {
//1.1.
c.takenby = none
//1.2.
c.passengers = none
//2.
c.enginestate = EngineOff
//3.
c.reservationtime = More1h
//4.
c.takenby.payment.total = Receipt
c.takenby.payment.charges = (c.takenby.payment.charges + Euro1)
}}



/* Occupied state implies:
1.1. RegUser in Car.takenby, 
1.2. can be passengers.
2. can be driven or parked
3. can be charged
4. no reservationtime
5. User don't have payment
*/
fact CarIsOccupiedConventions {
all c: Car | (c.occupationstate = Occupied) implies {
//1.1
c.takenby != none
//1.2.
// 2.
// no need to implement
// 3. 
// no need to implement
// 4.
c.reservationtime = none
//5.
no c.takenby.payment.total
}}





/*LostOccupation state implies
1.1 no RegUser in Car.takenby. 
1.2. Can be any passengers
2. Can be charged
3. 
USer must have payment
*/
fact CarIsLostOccupation {
all c: Car | (c.occupationstate = LostOccupation) implies {
//1.1.
c.takenby = none
//1.2.

//2.
c.enginestate = EngineOff
//3.
c.reservationtime = More1h
//4.
c.takenby.payment.total = Receipt
}}





/* Released state implies:
1. no RegUser in Car.takenby, no passengers
2. engine is off
3. can be charged
4. User must have payment
5. no time
*/
fact CarIsReleasedConventions {
all c: Car |  c.occupationstate = Released => {
//1.
c.takenby = none
//2.
c.enginestate = EngineOff
//3. 
// no need to implement
//4. 
c.takenby.payment.total = Receipt
//5.
c.reservationtime = none
}}



//chargingstate: one CarChargingState, // wether car is charging or not 
/* Charging state:
1. <=> car is parked
*/
fact CarChargingConventions {
//1.
all c: Car | (c.chargingstate = Charging) implies (c.parked != Driven)
}



/* NotCharging state:
1. car can be either parked or driving
*/
// NO NEED TO IMPLEMENT



//takenby: lone RegUser, // car can either have a RegUser or not
/*
1. user != non implies states


*/
fact TakenByConvention {
all c: Car | (no c.takenby) implies 
(c.occupationstate = Available) or (c.occupationstate = LostReservation) or (c.occupationstate = LostOccupation)
}

//passengers: some Person, // can carry some persons
/*
*/


//battery: one BatteryFulness, // battery fulness
/*
1. number of batteries must be equal to number of cars
*/

//parked: one Parked,
/*
AnyParkingArea:
1. 
*/ 

/*
SpecialParkingArea:
1. && Car.chargingstate = Charging => see REQUIREMENTS
*/ 




/*
Driving:
1. must have at least 1 passenger - RegUser
2. Car must be occupied 
3. NotCharging state
4. What about 2 passengers?
5. Engine must be on
*/ 
fact CarIsDrivenConventions {
all c: Car | (c.parked = Driven) implies {
//1.
#c.takenby > 0
c.takenby in c.passengers
//2.
c.occupationstate = Occupied
//3.
c.chargingstate = NotCharging
//4.
// ????
//5.
c.enginestate = EngineOn
}}


// enginestate: one CarEngineState
/*
EngineOn:
1. Car must be occupied
*/ 
/*
EngineOff:
1. must be parked
*/ 
fact CarEngineConventions {
all c: Car | (c.enginestate = EngineOn) implies {
//1.
c.occupationstate = Occupied
} else {
//1.
c.parked != Driven
}}



/* MERGED INTO ONE ABOVE
fact CarEngineOffConventions {
all c: Car | c.enginestate = EngineOff implies {
//1.
c.parked != Driven
}}
*/

//reservationtime: lone Time
/* Less1h:
1. <=> EngineOff && Occupied || Reserved
2. passengers can either be in the car or not
*/ 
fact CarLess1hTimeConventions {
all c:Car | (c.reservationtime = Less1h) implies {
c.enginestate = EngineOff // to run a countdown engine must be off
((c.occupationstate = Occupied) or (c.occupationstate = Reserved))
}}


/* More1h:
1. <=> EngineOff && LostResevation || LostOccupation
2. passengers can either be in the car or not
*/ 
fact CarMore1hTimeConventions {
all c:Car | (c.reservationtime = More1h) implies {
c.enginestate = EngineOff
((c.occupationstate = LostOccupation) or (c.occupationstate = LostReservation))
}}


/*
fact NumberOfPersonsInTheCar {
all c: Car { 
// NOTE: Number of RegUsers is restricted in Car definition
c.takenby != none implies #c.passengers <= 4 else // If the car is taken by RegUser, it can take at most 4 persons more
#c.passengers = 0 // if car is not taken by RegUser, no one can be in the car 
}}
*/
// ============================================================================

// REQUIREMENTS
// ============================================================================

// 2 passengers discount????
fact More2PassengersDiscount {
//all c: Car, p: Payment | (c.occstate = Occupied) //&& (#c.passengers >= 3) implies p.discounts + Discount10Percent
}
// 50% full battery discount
fact More50PercentEnergyDiscount{
all c: Car, oc: c.occupationstate, p: Payment | ((( oc = Released) or (oc = LostOccupation) or (oc = LostReservation)) && (c.battery = More50)) implies p.discounts = (p.discounts + Discount20Percent)
}
// Charging on the special parking zone discount
fact ChargingOfTheCarDiscount {
all c: Car, oc: c.occupationstate, p: Payment | ((( oc = Released) or (oc = LostOccupation) or (oc = LostReservation)) && (c.chargingstate = Charging) && (c.parked = SpecialParkingArea)) implies p.discounts = (p.discounts + Discount30Percent) // We suppose that charging of the car can only be done on the special parking area
//
}

// ============================================================================

pred show (){
#Car = 2
#RegUser = 3
#Receipt = 2
}


run show 
