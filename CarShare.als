// Boolean
abstract sig Bool {}
sig True extends Bool {}
sig False extends Bool {}



// Users
abstract sig Person{}
sig RegUser extends Person {
car: lone Car

}
sig UnregUser extends Person {}{ // unregistered users cannot use a car (can be done in Reqs)

}

// Car occupation states
abstract sig CarOcState {}
sig Available extends CarOcState {}
sig Reserved extends CarOcState {}
sig Occupied extends CarOcState {}
// Car charging states
abstract sig CarChState {}
sig Charg extends CarChState {}
sig Ncharg extends CarChState {}
// Car 

// Car
sig Car {
occstate: one CarOcState, // each car has 1 occupation state
chastate: one CarChState, // each car has 1 charging state
taken: lone RegUser, // car can either have a RegUser or not
passengers: some Person // can carry some more 

} { 
no RegUser in taken implies state CarState = Available // (Not sure) if no RegUser is in the Car, then Car is available 
#taken <= 1 // redunfant?
}




fact NumberOfPersonsInTheCar {
all c: Car { 
// Number of RegUsers is restricted in Car definition
RegUser in c.taken implies #Car.passengers <= 5 // If the car is taken by RegUser, itcan take at most 5 persons
no RegUser in c.taken implies #Car.passengers = 0 // if car is not taken by RegUser, no one can be in the car 
// (can be written in more compact way??)
}}


