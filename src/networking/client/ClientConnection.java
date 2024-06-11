package networking.client;

import networking.protocol.Protocol;
import java.io.IOException;

/**
 * The connection between the client and the server on the client side.
 */
public class ClientConnection extends networking.SocketConnection {
    private final Client client;

    /**
     * constructor for the ClientConnection. Is created at the same time as the client.
     * @param address the address for the client to connect to
     * @param port the port on which to connect to the server
     * @param client the client for this specific connection
     * @throws IOException if an I/O error occurs while establishing the connection
     */
    public ClientConnection(String address, int port, Client client) throws IOException {
        super(address,port);
        this.start();
        this.client = client;
    }

    /**
     * Sends a hello message to the server.
     *
     * @param clientName the name of the client wanting to connect
     */
    protected void sendHello(String clientName){
        sendMessage(Protocol.HELLO + Protocol.SEPARATOR + clientName);
    }

    /**
     * Sends a username message to the server.
     *
     * @param username the username to be sent
     */
    public void sendUsername(String username) {
        sendMessage(Protocol.LOGIN + Protocol.SEPARATOR + username);
    }

    /**
     * Sends the list command to the server
     */
    public void sendList(){sendMessage(Protocol.LIST);}

    /**
     * Sends the list command to the server
     */
    public void sendQueue(){sendMessage(Protocol.QUEUE);}

    /**
     * Sends the move command to the server
     */
    public void sendMove(String index){sendMessage(Protocol.MOVE + Protocol.SEPARATOR + index);}
    /**
     * Handles a message received from the connection.
     *
     * @param message the message received from the connection
     */
    @Override
    protected void handleMessage(String message) {
        client.receiveMessage(message);
    }

    /**
     * Handles a disconnect from the connection, i.e., when the connection is closed.
     */
    @Override
    protected void handleDisconnect() {
        client.handleDisconnect();
    }
}
