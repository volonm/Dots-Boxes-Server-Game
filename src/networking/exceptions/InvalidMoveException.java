package networking.exceptions;

import networking.protocol.Protocol;

/**
 * The InvalidMoveException class is a custom exception that represents an error condition
 * when an invalid move is detected in the networking game.
 * This exception can be thrown when a player attempts to make an illegal move, it is not their turn, or they are playing as computer
 */
public class InvalidMoveException extends RuntimeException {

    /**
     * Constructs a new InvalidMoveException with the specified error message.
     *
     * @param message the specified error message
     */
    public InvalidMoveException(String message) {
        super(Protocol.ERROR + Protocol.SEPARATOR + message);
    }
}
