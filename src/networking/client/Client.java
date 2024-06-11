package networking.client;

import game.model.GameImpl;
import game.model.Mark;
import game.model.Move;
import game.model.MoveGame;
import networking.exceptions.InvalidMoveException;
import networking.protocol.Protocol;

import java.io.IOException;
import java.util.List;
import java.util.Random;

/**
 * The client for Dots & Boxes
 * handles all user input and server response
 */
public class Client {
    protected ClientConnection clientConnection;
    protected String username;
    protected String opponent;
    protected GameImpl game;
    protected Mark mark;
    protected ClientListener listener;
    protected String name = "Joris' & Volodymyr's client";
    protected boolean connected;
    protected boolean turn;
    protected boolean active;

    /**
     * Constructor for the game client.
     *
     * @param address the address of the server
     * @param port    the port to connect to
     * @throws IOException if an I/O error occurs while creating the ClientConnection
     */
    public Client(String address, int port) throws IOException {
        clientConnection = new ClientConnection(address, port, this);
    }

    /**
     * Delegates the "hello" message to the server through the clientConnection.
     */
    public void sendHello(){
        clientConnection.sendHello(name);
    }

    /**
     * Sends a username to the server.
     *
     * @param username the username to be sent
     */
    public void sendUsername(String username) {
        clientConnection.sendUsername(username);
        this.username = username;
    }

    /**
     * Handles a message received from the server.
     *
     * @param message the chat message received from the server
     */
    public void receiveMessage(String message) {
        String[] split = message.split(Protocol.SEPARATOR);
        String command = split[0];

        switch (command) {
            case Protocol.LOGIN:
                handleLogin(split);
                break;
            case Protocol.LIST:
                handleList(split);
                break;
            case Protocol.ALREADYLOGGEDIN:
                handleAlreadyLoggedIn(split);
                break;
            case Protocol.GAMEOVER:
                handleGameOver(message);
                break;

            default:
                // Do nothing, server sent an invalid message
                break;
        }
    }

    /**
     * Sends the specified command to the server
     *
     * @param command the command to be sent
     */
    public void sendCommand(String command) {
        String[] split = command.split(Protocol.SEPARATOR);
        String commandType = split[0].toUpperCase();

        switch (commandType) {
            case Protocol.LIST:
                handleListCommand();
                break;
            case Protocol.MOVE:
                handleMoveCommand(split);
                break;
            case "HINT":
                provideHint();
                break;
            default:
                listener.message(Protocol.ERROR + Protocol.SEPARATOR + "Not a command");
                break;
        }
    }

    /**
     * Sends list command to the server.
     */
    void handleListCommand() {
        clientConnection.sendList();
    }

    /**
     * send the move command together with the index to play to the server
     * if the client is not playing as computer
     * @param split the command to process
     */
    void handleMoveCommand(String[] split) {
        try {
            if (active) {
                 if (!turn) {
                    throw new InvalidMoveException("Not your turn");
                } else {
                    processValidMove(split);
                }
            } else {
                throw new InvalidMoveException("No game is active");
            }
        } catch (InvalidMoveException e) {
            // Handle the exception, e.g., display an error message to the user
            listener.message(e.getMessage());
        }
    }

    /**
     * Sends move command to the server if the move is valid.
     * @param split the command containing the move
     */
    private void processValidMove(String[] split) {
        try {
            if (game.isValidMove(new MoveGame(Integer.parseInt(split[1]), mark))) {
                clientConnection.sendMove(split[1]);
            } else {
                throw new InvalidMoveException("Move not valid");
            }
        } catch (InvalidMoveException e) {
            // Handle the exception, e.g., display an error message to the user
            listener.message(e.getMessage());
        }
    }

    /**
     * provides a random move you could play
     */
    void provideHint() {
        if (!active) {
            listener.message(Protocol.ERROR + Protocol.SEPARATOR + "Not in game");
        } else {
            List<Move> validMoves = game.getValidMoves();
            if (!validMoves.isEmpty()) {
                Random random = new Random();
                int randomIndex = random.nextInt(validMoves.size());
                Move randomMove = validMoves.get(randomIndex);
                listener.message("Move you could play: " + randomMove.getIndex());
            } else {
                listener.message(Protocol.ERROR + Protocol.SEPARATOR + "No valid moves available");
            }
        }
    }

    /**
     * handles LOGIN command from the server
     * @param split the confirmation from the server
     */
    void handleLogin(String[] split) {
        connected = true;
        listener.message(split[0]);
    }

    /**
     * Handles the list of online players provided by the server
     * @param split the full message from the server
     */
    void handleList(String[] split) {
        listener.message("Online players:");
        for (int i = 1; i < split.length; i++) {
            listener.message(split[i]);
        }
    }

    /**
     * Handles the ALREADYLOGGEDIN command from the server
     * @param split the command from the server
     */
    void handleAlreadyLoggedIn(String[] split) {
        username = "";
        listener.message(split[0]);
    }

    /**
     * Handles the GAME OVER command from the server
     * @param message the message from the server
     */
    void handleGameOver(String message) {
        active = false;
        turn = false;
        listener.message(game.getBoard().toString());
        listener.message(message);

    }

    /**
     * Handles the client disconnecting
     */
    public void handleDisconnect() {
        System.out.println(Protocol.ERROR + Protocol.SEPARATOR + "client disconnect");
        listener.connectionLost();
    }

    /**
     * Closes the connection to the server.
     */
    public void close() {
        clientConnection.close();
    }
}
