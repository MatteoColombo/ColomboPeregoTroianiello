void createMeeting(String name, String description, MeetingType type, Location location, Date start_hour, Date end_hour){
    result = true;
    /*Checks if there is already an event scheduled in the given time and in case, it gives a warning*/
    if(overlaps(start_hour,end_hour)){
        result=false;
    }
    else{
        // Gets the previous scheduled meeting
        Meeting next= getNextMeeting(end_hour);
        // Gets the next scheduled meeting 
        Meeting prev= getPrevMeeting(start_hour);
    
        /* Checks if the meeting is reachable in time from the previous one and if it doesn't make the following unreachable */
        if(reachable(start_hour,location,prev) && !makesNextUnreachable(end_hour,location,next)){

            Meeting meeting = new Meeting(name,description, type, location, start_hour, end_hour);
            //Computes the journey from the previous to the next meeting
            Journey journey1 = computeJourney(prev, meeting);
            //Computes the journey from the meeting to the following one
            Journey journey2 = computeJourney(meeting, next);
            
            //Checks if there is enough time left for the lunch break
            if(leavesTimeForLunch(meeting,journey1,journey2)){
                /* If everything is ok, adds the meeting and the journeys to the db and then creates the lunch if it doesn't exist*/
                addMeetingToDB(meeting);
                updateJourneys(journey1,journey2);
                if(!lunchExists()){
                    addLunch(start_hour);
                }
            }else{
                showWarning(LUNCH);
            }

        }else{
            showWarning(UNREACHABLE);
        }
}