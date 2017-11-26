Journey findBestJourney(List journeys, Weather weatherInfo, Preferences userPreferences, Meeting meeting){
    List validJourneys;

    for(i=0; i < journeys.size(); i++){
        boolean valid = true;
        Journey j = journeys.get(i);
        Segment segments = j.getSegments();
        for(h=0; h< segments.length && valid; h++){
            valid = (segments[h].getTravelMean()).checkIfConstraintsAreRespected(segments[h],weatherInfo, meeting);
        }
        if(valid){
            validJourneys.add(j);
        }
    }

    if(userPreferences.getFootprintPref()){
        validJourneys.orderByFootprint("asc");
    }else{
        validJourneys.orderByDuration("asc")
    }

    if(meeting.getType().hasPreference()){
        TravelMean preferedTravelMean= meeting.getType().getPreferedTravelMean();
        int index = validJourneys.getIndexJourneyWPreferedTM(preferedTravelMean);
        if(index>0){
            TravelMean.moveToFirst(index);
        }
    }

    return validJourneys.get(0);
}