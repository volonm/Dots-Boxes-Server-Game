package networking.server;

import game.model.MoveGame;
import networking.protocol.Protocol;
import networking.SocketConnection;

import java.io.IOException;
import java.net.Socket;

/**
 * ServerConnection class represents the communication link between the server and a specific client.
 * It extends the SocketConnection class and is responsible for handling messages received from the client.
 */
public class ServerConnection extends SocketConnection {

    /**
     * Private ClientHandler instance to connect the ServerConnection with ClientHandler.
     */
    private ClientHandler clientHandler;

    /**
     * Create a new SocketConnection. This is not meant to be used directly.
     *
     * @param socket the socket for this connection
     * @throws IOException if there is an I/O exception while initializing the Reader/Writer objects
     */
    protected ServerConnection(Socket socket) throws IOException {
        super(socket);
    }

    /**
     * Handles the message split and calls the specific methods based on the command received.
     *
     * @param message the message received from the connection.
     */
    @Override
    protected void handleMessage(String message) {
        String[] parts = message.split(Protocol.SEPARATOR);
        if (parts.length >= 1) {
            switch (parts[0]) {
                case Protocol.HELLO:
                    helloPartition(parts);
                    break;
                case Protocol.LOGIN:
                    loginPartition(parts);
                    break;
                case Protocol.LIST:
                    clientHandler.handleList();
                    break;
                case Protocol.QUEUE:
                    clientHandler.handleQueue();
                    break;
                case Protocol.MOVE:
                    moveSeparation(parts);
                    break;
                case Protocol.NEWGAME:
                    clientHandler.handleNewGame();
                    break;
                default:
                    clientHandler.sendCommand(Protocol.ERROR);
                    break;
            }
        }
    }

    /**
     * Handles the partition for the received hello command and calls needed method in clientHandler.
     *
     * @param parts split of initially received message.
     */
    private void helloPartition(String[] parts) {
        if (parts.length > 1) clientHandler.handleHello(parts[1]);
        else sendMessageClient(Protocol.ERROR);
    }

    /**
     * Handles the partition for the received Login command and calls needed method in clientHandler.
     *
     * @param parts split of initially received message.
     */
    private void loginPartition(String[] parts) {
        if (parts.length > 1) clientHandler.handleLogin(parts[1]);
        else sendMessageClient(Protocol.ERROR);
    }

    /**
     * Handles the partition for the received Move command, creates the move
     * and calls the needed method in clientHandler.
     *
     * @param parts split of initially received message.
     */
    private void moveSeparation(String[] parts) {
        if (clientHandler.isInGame()) {
            try {
                clientHandler.handleMove(new MoveGame(Integer.parseInt(parts[1]), clientHandler.getMark()));
            } catch (NumberFormatException e) {
                sendMessageClient(Protocol.ERROR);
            }
        }
    }

    /**
     * Sends a message to the connected client. Is used to send all the data to connected client.
     *
     * @param message the chat message to be sent
     */
    public void sendMessageClient(String message) {
        sendMessage(message);
    }


    @Override
    protected void handleDisconnect() {
        clientHandler.handleDisconnect();
        System.out.println("Client Disconnected.");
    }

    /**
     * Sets the clientHandler of the ServerConnection to the given clientHandler.
     *
     * @param clientHandler clientHandler to set.
     */
    public void setClientHandler(ClientHandler clientHandler) {
        this.clientHandler = clientHandler;
    }
}
