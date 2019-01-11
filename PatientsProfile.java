
//Given("^User is trying to see patient's profile$")

public class PatientsProfile {
    private User[] Users;
    private int patientsProfile;

    /*@ normal_behavior
      @ determines u, u.profile,
      @            hasPrivilege(u),
      @            (hasPrivilege(u) ? patientsProfile : 0)
      @        \by \itself;
      @*/

//When("^User has access privilege to patient's profile$")
    
    public void getPatientsProfile(User u) {
        if (hasPrivilege(u)) {
            u.setProfile(patientsProfile);
        }
    }

    /*@ normal_behavior
      @ ensures \result ==
      @         (\exists int i; 0 <= i && i < Users.length;
      @                                             Users[i] == u);
      @*/
    private /*@ pure */ boolean hasPrivilege(User u) {
        /*@ loop_invariant 0 <= i && i <= Users.length;
          @ loop_invariant
          @     (\forall int j; 0 <= j && j < i; Users[j] != u);
          @ assignable \nothing;
          @ decreases Users.length - i;
          @*/
        for (int i = 0; i < Users.length; i++) {
            if (Users[i] == u) {
                return true;
            }
        }
        return false;
    }
//Then("^User can read patient's profile$")

    public class User {
        private /*@ spec_public */ int profile;

        void setProfile(int profile) {
            this.profile = profile;
        }
    }
}
