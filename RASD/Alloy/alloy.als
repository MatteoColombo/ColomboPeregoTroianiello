
sig Position{}
sig Text{}

sig Time{
    timestamp: one Int,
    day: one Int
}
{
    day > 0
    timestamp > 0
}

abstract sig Event{
    start: one Time,
    end: one Time
}
{
    start.timestamp < end.timestamp
    start.day = end.day
}

sig Break extends Event{
    slotstart: one Time,
    slotend: one Time
}
{
    slotstart.timestamp <= start.timestamp
    slotend.timestamp >= end.timestamp
    slotstart.timestamp < slotend.timestamp
    slotend.day= slotstart.day
    slotstart.day = start.day
}

sig Lunch extends Break{}

sig Meeting extends Event{
    name: one Text,
    desc: one Text,
    position: one Position,
    type: one EventType
}

abstract sig EventType{
    prefers: one TravelMean
}
one sig Family extends EventType{}
one sig Work extends EventType{}
one sig Personal extends EventType{}

one sig User{
	home: one Home,
	currpos: one Position,
	passes: set TravelPass
}

one sig Home{
	pos: one Position
}

sig Journey{
	user: one User,
	startmeet: lone Meeting,
	endmeet: one Meeting,
	start: one Position,
	end: one Position,
	startseg: one Segment,
	endseg: one Segment,
	intseg: set Segment,
	day: one Int
}{
    start != end
   end = endmeet.position
	startmeet != endmeet
	#startmeet = 1 implies start = startmeet.position && (startmeet.start).day = (endmeet.start).day 
																&& (startmeet.start).timestamp < (endmeet.start).timestamp
								else start = (user.home).pos
  
		day = (endmeet.start).day
	
    //Concatenation of seg
    startseg.start=start
    endseg.end = end
    no x: intseg | x=startseg || x=endseg
    lone x: intseg | x.start = startseg.end
    lone x: intseg | endseg.start = x.end
    no x: intseg | startseg.start = x.end
    no x:intseg | x.start= endseg.end
    all x: intseg | x.end = endseg.start 
        or one x1: intseg | x.end = x1.start 
    all x: intseg | x.start = startseg.end 
        or one x1: intseg | x.start = x1.end 
    #intseg = 0 implies (startseg = endseg or startseg.end=endseg.start)
}

sig Segment{
	id: one Int,
	start: one Position,
	end: one Position,
	mean: one TravelMean,
	pass: lone TravelPass,
	journey: one Journey
}
{
    id >0
    start != end
	journey.day>= (pass.start).day
	journey.day <= (pass.end).day
}

abstract sig TravelMean{
	constr: set Constraint,
	pollution: one Level
}
abstract sig PublicTransport extends TravelMean{}
one sig Bus extends PublicTransport{}
one sig Train extends PublicTransport{}
abstract sig SharedVehicle extends TravelMean{}
one sig Bike extends SharedVehicle{}
abstract sig OwnedVehicle extends TravelMean{}
one sig Car extends OwnedVehicle{}
one sig Walk extends OwnedVehicle{}

abstract sig Constraint{}

abstract sig Level{}
one sig Level1 extends Level{}
one sig Level2 extends Level{}
one sig Level3 extends Level{}

sig TravelPass{
	start: one Time,
	end: one Time,
	mean: one PublicTransport
}
{
    start.day <= end.day 
}

//FACTS
---------------------------------------------------

fact allEventDisjoint{
	all disj e1,e2: Event | ((e1.start).timestamp) > ((e2.end).timestamp) || ((e2.start).timestamp) > ((e1.end).timestamp)
}

fact noSegWithSameId{
	no disj s1,s2: Segment | s1.id = s2.id
}

fact eachSegBelongsToOneJourney{
	all s: Segment | one j:Journey | (s in j.intseg || s=j.startseg || s=j.endseg)
	all s: Segment |one j:Journey | s.journey = j
}

fact atMostOneLunchADay{
	all disj l1,l2: Lunch | (l1.start).day != (l2.start).day
	all m:Meeting | one l:Lunch | (l.start).day = (m.start).day
}

fact aMeetingNeedsAJourney{
	all m: Meeting | one j: Journey | j.endmeet = m
	all m: Meeting | lone j: Journey | j.startmeet = m
}

fact travelPassMustBeOwned{
	all p: TravelPass | one u:User | p in u.passes
}

fact atMostOneJourneyAtADayStartsFromHome{
	all disj j1,j2: Journey | (j1.day=j2.day && #j1.startmeet = 0) implies #j2.startmeet = 1
}


fact journeyNumber{
	#Journey = #Meeting
}


//ASSERTIONS
-----------------------------------------------------

assert allEventsDisjoint{
	no disj e1,e2: Event | (e2.start.timestamp > e1.start.timestamp &&  e2.start.timestamp < e1.end.timestamp)
											|| (e2.end.timestamp > e1.start.timestamp &&  e2.end.timestamp < e1.end.timestamp)
}

assert ifThereIsAMeetingThereIsLunch{
	no m:Meeting | all l:Lunch | (l.start).day != (m.start).day
}

assert lunchIsAlwaysInTheLunchSlot{
	no l:Lunch | l.start.timestamp < l.slotstart.timestamp ||  l.end.timestamp > l.slotend.timestamp
}

assert journeyFromHomeFirstOfTheDay{
	no disj j1,j2: Journey | j1.day=j2.day && #j1.startmeet = 0 && #j2.startmeet = 0
}

assert usedTicketsAreValidDuringTheSegment{
	all s:Segment | #s.pass = 1 implies s.pass.start.day <= s.journey.day && s.pass.end.day >= s.journey.day
}

check lunchIsAlwaysInTheLunchSlot for 6 but 5 int
check ifThereIsAMeetingThereIsLunch for 6 but 5 int
check allEventsDisjoint for 6 but 5 int
check journeyFromHomeFirstOfTheDay for 6 but 5 int
check  usedTicketsAreValidDuringTheSegment for 6 but 5 int


//PREDICATES
-----------------------------------------------------
pred show(){
	(Meeting.start).day=3
	#Meeting = 2 
	#Segment = 3
	#Position = 4
	#TravelPass = 1
}

run show for 6 but 5 int
