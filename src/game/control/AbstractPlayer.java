package game.control;

import game.model.Mark;

/**
 * A player of a game.
 */
public abstract class AbstractPlayer implements Player {
    private final String name;
    private final Mark mark;

    /**
     * Creates a new Player object with the given Mark and Name.
     */
    /*@ requires name != null;
        ensures getName() == name && getMark() == m;
    @*/
    protected AbstractPlayer(String name, Mark m) {
        this.name = name;
        this.mark = m;
    }

    /**
     * Returns the name of the player.
     *
     * @return the name of the player
     */
    //@pure;
    public String getName() {
        return name;
    }

    /**
     * Returns the Mark of the Player.
     *
     * @return mark of the Player.
     */
    //@pure;
    public Mark getMark(){return this.mark;}


    /**
     * Returns a representation of a player, i.e., their name
     *
     * @return the String representation of this object
     */
    @Override
    public String toString() {
        return "Player " + name;
    }
}
