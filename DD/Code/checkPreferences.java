boolean checkPreferences(List preferences, List meetings){
    today= getDate().day;
    for each pref in preferences{
        if(generatesConflicts(pref, today, meetings)){
            return false;
        }   
    }
    return true;
}