import React, {
  useState,
  useEffect
} from 'react';
import _  from 'lodash';
import { Box, Row, Text, BaseImage } from '@tlon/indigo-react';
import { uxToHex } from '~/logic/lib/util';
import { Sigil } from '~/logic/lib/sigil';

export const ShareProfile = (props) => {
  const {
    api,
    showBanner,
    setShowBanner,
    group,
    groupPath,
    recipients
  } = props;

  const image = (props?.our?.avatar)
  ? (
    <BaseImage
      src={props.our.avatar}
      width='24px'
      height='24px'
      borderRadius={2}
      style={{ objectFit: 'cover' }} />
  ) : (
    <Row
      p={1}
      alignItems="center"
      borderRadius={2}
      backgroundColor={!!props.our ? `#${uxToHex(props.our.color)}` : "#000000"}>
      <Sigil
        ship={window.ship}
        size={16}
        color={!!props.our ? `#${uxToHex(props.our.color)}` : "#000000"}
        icon />
    </Row>
  );

  const onClick = async () => {
    if(typeof recipients === 'string') {
      const [,,ship,name] = recipients.split('/');
      await api.contacts.allowGroup(ship,name);
      if(ship !== `~${window.ship}`) {
        await api.contacts.share(ship);
      }
    } else if(recipients.length > 0) {
      await api.contacts.allowShips(recipients);
      await Promise.all(recipients.map(r => api.contacts.share(r)))
    } 
    props.onShare();
  };

  return props.recipients?.length > 0 ? (
    <Row
      height="48px"
      alignItems="center"
      justifyContent="space-between"
      borderBottom={1}
      borderColor="lightGray"
      flexShrink={0}
    >
      <Row pl={3} alignItems="center">
        {image}
        <Text verticalAlign="middle" pl={2}>Share private profile?</Text>
      </Row>
      <Box pr={2} onClick={onClick}>
        <Text color="blue" bold cursor="pointer">Share</Text>
      </Box>
    </Row>
  ) : null;
};