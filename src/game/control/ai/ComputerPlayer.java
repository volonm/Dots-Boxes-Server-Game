package game.control.ai;

import game.control.AbstractPlayer;
import game.model.Mark;
import game.model.Game;
import game.model.Move;

/**
 * The ComputerPlayer class is a computer-controlled player It extends the AbstractPlayer class
 * and uses a specified strategy to determine its moves during the game.
 */
public class ComputerPlayer extends AbstractPlayer {

    private final Strategy strategy;

    /**
     * The constructor which creates the Computer Player with the given strategy and mark.
     *
     * @param s strategy of the Computer Player.
     * @param m mark of the Computer Player.
     */
    //@ requires s != null && m != null;
    //@ ensures super.getName().contains(s.getName()) && super.getMark() == m;
    public ComputerPlayer(Strategy s, Mark m) {
        super("Bot: " + s.getName(), m);
        this.strategy = s;
    }

    /**
     * Determines the next move for the ComputerPlayer using its specified strategy.
     *
     * @param game the Game instance in which the ComputerPlayer is participating
     * @return the Move determined by the strategy for the next move
     */
    @Override
    public Move determineMove(Game game) {
        return strategy.determineMove(game);
    }
}
